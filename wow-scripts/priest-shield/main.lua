function()
  function auraValue(sid)
    return select(17, UnitBuff("player", GetSpellInfo(sid))) or 0
  end
  function toK(v)
    return math.floor(v / 1000)
  end
  -- XMO + PWS + MF
  return toK(auraValue(207472) + auraValue(17) + auraValue(194022))
end
