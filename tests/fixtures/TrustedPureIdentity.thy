theory TrustedPureIdentity
imports Pure
begin

lemma identity: "!!P::prop. PROP P ==> PROP P"
  by assumption

end
