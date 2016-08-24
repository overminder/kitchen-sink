(function()
  local gStore = omWeakAuraGlobalStore or {}
  omWeakAuraGlobalStore = gStore

  return function(xs, ...)
    return gStore.damageTakenInTheLast5Seconds
  end
end)()
