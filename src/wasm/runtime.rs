//! WASM runtime for search-only plugin metadata.
//!
//! Tactic execution and proof reconstruction are not implemented. Lookup
//! returns legacy metadata handles, never a kernel theorem or proof acceptance.

use std::sync::Arc;

use wasmtime::{Caller, Engine, FuncType, Linker, Memory, Module, Store, TypedFunc, Val, ValType};

use super::{
    Plugin, PluginContext,
    host::{HOST_FACT_KIND, HOST_LOOKUP, ThmTable},
};
use crate::core::thm::Thm;

// =========================================================================
// Runtime state
// =========================================================================

/// State held inside the wasmtime Store.
struct RuntimeState {
    memory: Option<Memory>,
    ctx: PluginContext,
    search_facts: ThmTable,
}

// =========================================================================
// WasmRuntime
// =========================================================================

/// Manages a loaded WASM plugin instance.
pub struct WasmRuntime {
    _engine: Engine,
    store: Store<RuntimeState>,
    /// The `apply_tactic` function exported by the plugin.
    _apply_func: TypedFunc<(i32, i32), i32>,
    /// Plugin metadata.
    name: String,
    version: String,
}

impl WasmRuntime {
    /// Execution fuel budget, not a wall-clock deadline or memory limit.
    pub const DEFAULT_FUEL: u64 = 10_000_000;

    /// Load a WASM plugin from raw bytes.
    ///
    /// The .wasm module must export:
    /// - `apply_tactic(goal_ptr: i32, goal_len: i32) -> i32`: returns result pointer
    /// - `memory`: the WASM linear memory
    pub fn load(name: String, version: String, wasm_bytes: &[u8]) -> Result<Self, String> {
        let mut config = wasmtime::Config::default();
        config.consume_fuel(true);

        let engine = Engine::new(&config).map_err(|e| format!("failed to create engine: {e}"))?;

        let module = Module::from_binary(&engine, wasm_bytes)
            .map_err(|e| format!("failed to compile WASM module: {e}"))?;

        let mut store = Store::new(
            &engine,
            RuntimeState { memory: None, ctx: PluginContext::new(), search_facts: ThmTable::new() },
        );

        // Set fuel limit
        store.set_fuel(Self::DEFAULT_FUEL).map_err(|e| format!("failed to set fuel: {e}"))?;

        // Create linker and define host functions
        let mut linker = Linker::new(&engine);
        Self::define_host_functions(&engine, &mut linker)?;

        let instance = linker
            .instantiate(&mut store, &module)
            .map_err(|e| format!("failed to instantiate module: {e}"))?;

        // Get the exported memory
        let memory =
            instance.get_memory(&mut store, "memory").ok_or("plugin must export 'memory'")?;
        store.data_mut().memory = Some(memory);

        // Get the exported function
        let apply_func = instance
            .get_typed_func::<(i32, i32), i32>(&mut store, "apply_tactic")
            .map_err(|e| format!("plugin must export 'apply_tactic': {e}"))?;

        Ok(WasmRuntime { _engine: engine, store, _apply_func: apply_func, name, version })
    }

    /// Define host functions callable from WASM.
    fn define_host_functions(
        engine: &Engine,
        linker: &mut Linker<RuntimeState>,
    ) -> Result<(), String> {
        // Search-only lookup: a positive handle indexes legacy metadata;
        // -1 denotes unknown names, invalid memory/UTF-8 or exhausted handles.
        let lookup_type = FuncType::new(engine, [ValType::I32, ValType::I32], [ValType::I32]);
        linker
            .func_new(
                "env",
                HOST_LOOKUP,
                lookup_type,
                |mut caller: Caller<'_, RuntimeState>, params: &[Val], results: &mut [Val]| {
                    let ptr = params[0].unwrap_i32();
                    let len = params[1].unwrap_i32();
                    results[0] = Val::I32(Self::lookup_search_fact(&mut caller, ptr, len));
                    Ok(())
                },
            )
            .map_err(|e| format!("failed to define host_lookup: {e}"))?;

        // Classification of a search handle, never a proof acceptance code.
        let kind_type = FuncType::new(engine, [ValType::I32], [ValType::I32]);
        linker
            .func_new(
                "env",
                HOST_FACT_KIND,
                kind_type,
                |caller: Caller<'_, RuntimeState>, params: &[Val], results: &mut [Val]| {
                    let handle = params[0].unwrap_i32();
                    let kind =
                        caller.data().search_facts.get(handle).map(|fact| fact.kind().abi_code());
                    results[0] = Val::I32(kind.unwrap_or(-1));
                    Ok(())
                },
            )
            .map_err(|e| format!("failed to define host_fact_kind: {e}"))?;

        // host_debug: print a debug message
        let debug_type = FuncType::new(engine, [ValType::I32, ValType::I32], []);
        linker
            .func_new(
                "env",
                "host_debug",
                debug_type,
                |caller: Caller<'_, RuntimeState>, params: &[Val], _results: &mut [Val]| {
                    let ptr = params[0].unwrap_i32() as usize;
                    let len = params[1].unwrap_i32() as usize;
                    if let Some(mem) = &caller.data().memory {
                        let mut buf = vec![0u8; len.min(4096)];
                        let _ = mem.read(&caller, ptr, &mut buf);
                        let msg = String::from_utf8_lossy(&buf);
                        tracing::debug!("[wasm plugin] {msg}");
                    }
                    Ok(())
                },
            )
            .map_err(|e| format!("failed to define host_debug: {e}"))?;

        Ok(())
    }

    /// Read a plugin-supplied name and return a legacy search handle.
    fn lookup_search_fact(caller: &mut Caller<'_, RuntimeState>, ptr: i32, len: i32) -> i32 {
        let (Ok(ptr), Ok(len)) = (usize::try_from(ptr), usize::try_from(len)) else {
            return -1;
        };
        if len > super::sdk::MAX_DATA_SIZE {
            return -1;
        }
        let Some(memory) = &caller.data().memory else {
            return -1;
        };
        let mut bytes = vec![0; len];
        if memory.read(&*caller, ptr, &mut bytes).is_err() {
            return -1;
        }
        let Ok(name) = std::str::from_utf8(&bytes) else {
            return -1;
        };
        let Some(fact) = caller.data().ctx.lookup(name).cloned() else {
            return -1;
        };
        caller.data_mut().search_facts.register(fact).unwrap_or(-1)
    }

    /// Tactic execution is unsupported; search metadata never counts as proof.
    pub fn call_tactic(&mut self, _state: &Thm, ctx: PluginContext) -> Result<Vec<Thm>, String> {
        self.store.data_mut().search_facts.clear();
        self.store.data_mut().ctx = ctx;
        Err("WASM tactic execution and proof reconstruction are not implemented".into())
    }
}

impl Plugin for WasmRuntime {
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        &self.version
    }

    fn apply(&self, state: &Thm, thms: &[Arc<Thm>]) -> Vec<Thm> {
        let _ = (state, thms);
        Vec::new()
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_runtime_load_invalid_module() {
        // Invalid WASM bytes
        let wasm_bytes: &[u8] = &[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];
        let result = WasmRuntime::load("test".into(), "0.1".into(), wasm_bytes);
        // Should fail (incomplete module) but not panic
        assert!(result.is_err());
    }

    #[test]
    fn host_lookup_known_legacy_fact_returns_metadata_only() {
        use wasmtime::MemoryType;

        let engine = Engine::default();
        let mut linker = Linker::new(&engine);
        WasmRuntime::define_host_functions(&engine, &mut linker).unwrap();

        let proposition = crate::core::thm::CTerm::certify(crate::core::term::Term::const_(
            "A",
            crate::core::types::Typ::base("prop"),
        ));
        let admitted = crate::core::thm::ThmKernel::admit(proposition, "test");
        let mut ctx = PluginContext::new();
        ctx.index_legacy("A".into(), &admitted);
        let mut store =
            Store::new(&engine, RuntimeState { memory: None, ctx, search_facts: ThmTable::new() });
        let memory = Memory::new(&mut store, MemoryType::new(1, None)).unwrap();
        memory.write(&mut store, 0, b"A").unwrap();
        store.data_mut().memory = Some(memory);

        let lookup = linker
            .get(&mut store, "env", HOST_LOOKUP)
            .unwrap()
            .into_func()
            .unwrap()
            .typed::<(i32, i32), i32>(&store)
            .unwrap();
        let handle = lookup.call(&mut store, (0, 1)).unwrap();
        assert!(handle > 0);
        assert_eq!(
            store.data().search_facts.get(handle).unwrap().kind(),
            super::super::host::LegacyFactKind::Admitted
        );
        let kind = linker
            .get(&mut store, "env", HOST_FACT_KIND)
            .unwrap()
            .into_func()
            .unwrap()
            .typed::<i32, i32>(&store)
            .unwrap();
        assert_eq!(
            kind.call(&mut store, handle).unwrap(),
            super::super::host::LegacyFactKind::Admitted.abi_code()
        );
        assert_eq!(kind.call(&mut store, -1).unwrap(), -1);
        assert_eq!(lookup.call(&mut store, (1, 1)).unwrap(), -1);
        assert_eq!(lookup.call(&mut store, (-1, 1)).unwrap(), -1);
        assert_eq!(lookup.call(&mut store, (i32::MAX, 1)).unwrap(), -1);
        store.data_mut().search_facts.clear();
        assert!(store.data().search_facts.get(handle).is_none());
        assert_eq!(kind.call(&mut store, handle).unwrap(), -1);
    }
}
