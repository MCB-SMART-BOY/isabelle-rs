//! WASM runtime — loads and executes .wasm plugins via wasmtime.
//!
//! ## Fuel metering
//!
//! Each WASM instruction consumes 1 fuel unit. The default limit is
//! 10_000_000 instructions (~10ms on modern hardware). When fuel
//! runs out, the plugin is terminated with an error.
//!
//! ## Memory model
//!
//! Plugins get a 64KB linear memory. They communicate with the host
//! by writing/reading to/from this memory via host function calls.

use std::sync::Arc;

use wasmtime::{
    Engine, Store, Module, Linker, Memory,
    Caller, TypedFunc, Val, ValType, FuncType,
};

use super::{Plugin, PluginContext};
use crate::core::thm::Thm;

// =========================================================================
// Runtime state
// =========================================================================

/// State held inside the wasmtime Store.
struct RuntimeState {
    /// Memory shared with the WASM module.
    memory: Option<Memory>,
    /// Plugin context (named theorems etc).
    #[allow(dead_code)]
    ctx: PluginContext,
}

// =========================================================================
// WasmRuntime
// =========================================================================

/// Manages a loaded WASM plugin instance.
pub struct WasmRuntime {
    _engine: Engine,
    #[allow(dead_code)]
    store: Store<RuntimeState>,
    /// The `apply_tactic` function exported by the plugin.
    _apply_func: TypedFunc<(i32, i32), i32>,
    /// Plugin metadata.
    name: String,
    version: String,
}

impl WasmRuntime {
    /// Maximum fuel (instructions) before timeout.
    pub const DEFAULT_FUEL: u64 = 10_000_000;

    /// Load a WASM plugin from raw bytes.
    ///
    /// The .wasm module must export:
    /// - `apply_tactic(goal_ptr: i32, goal_len: i32) -> i32`: returns result pointer
    /// - `memory`: the WASM linear memory
    pub fn load(name: String, version: String, wasm_bytes: &[u8]) -> Result<Self, String> {
        let mut config = wasmtime::Config::default();
        config.consume_fuel(true);

        let engine = Engine::new(&config)
            .map_err(|e| format!("failed to create engine: {e}"))?;

        let module = Module::from_binary(&engine, wasm_bytes)
            .map_err(|e| format!("failed to compile WASM module: {e}"))?;

        let mut store = Store::new(
            &engine,
            RuntimeState {
                memory: None,
                ctx: PluginContext::new(),
            },
        );

        // Set fuel limit
        store.set_fuel(Self::DEFAULT_FUEL)
            .map_err(|e| format!("failed to set fuel: {e}"))?;

        // Create linker and define host functions
        let mut linker = Linker::new(&engine);
        Self::define_host_functions(&engine, &mut linker)?;

        let instance = linker
            .instantiate(&mut store, &module)
            .map_err(|e| format!("failed to instantiate module: {e}"))?;

        // Get the exported memory
        let memory = instance
            .get_memory(&mut store, "memory")
            .ok_or("plugin must export 'memory'")?;
        store.data_mut().memory = Some(memory);

        // Get the exported function
        let apply_func = instance
            .get_typed_func::<(i32, i32), i32>(&mut store, "apply_tactic")
            .map_err(|e| format!("plugin must export 'apply_tactic': {e}"))?;

        Ok(WasmRuntime {
            _engine: engine,
            store,
            _apply_func: apply_func,
            name,
            version,
        })
    }

    /// Define host functions callable from WASM.
    fn define_host_functions(engine: &Engine, linker: &mut Linker<RuntimeState>) -> Result<(), String> {
        // host_lookup: look up a theorem by name
        // Signature: fn(name_ptr: i32, name_len: i32) -> i32
        let lookup_type = FuncType::new(
            engine,
            [ValType::I32, ValType::I32],
            [ValType::I32],
        );
        linker
            .func_new("env", "host_lookup", lookup_type, |_caller: Caller<'_, RuntimeState>, _params: &[Val], _results: &mut [Val]| {
                // TODO: read name from memory, look up in ctx, return thm_id
                _results[0] = Val::I32(0);
                Ok(())
            })
            .map_err(|e| format!("failed to define host_lookup: {e}"))?;

        // host_debug: print a debug message
        let debug_type = FuncType::new(
            engine,
            [ValType::I32, ValType::I32],
            [],
        );
        linker
            .func_new("env", "host_debug", debug_type, |caller: Caller<'_, RuntimeState>, params: &[Val], _results: &mut [Val]| {
                let ptr = params[0].unwrap_i32() as usize;
                let len = params[1].unwrap_i32() as usize;
                if let Some(mem) = &caller.data().memory {
                    let mut buf = vec![0u8; len.min(4096)];
                    let _ = mem.read(&caller, ptr, &mut buf);
                    let msg = String::from_utf8_lossy(&buf);
                    tracing::debug!("[wasm plugin] {msg}");
                }
                Ok(())
            })
            .map_err(|e| format!("failed to define host_debug: {e}"))?;

        Ok(())
    }

    /// Call the plugin's apply_tactic function.
    ///
    /// Currently returns an empty result — full implementation requires
    /// proper memory management between host and WASM.
    pub fn call_tactic(&mut self, _state: &Thm, _ctx: PluginContext) -> Result<Vec<Thm>, String> {
        // Full implementation would:
        // 1. Convert Goal → PluginGoal, serialize to JSON
        // 2. Write JSON bytes to WASM memory
        // 3. Call apply_tactic(ptr, len)
        // 4. Read result from WASM memory
        // 5. Deserialize PluginResult → Vec<Vec<Goal>>
        Ok(Vec::new())
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
}
