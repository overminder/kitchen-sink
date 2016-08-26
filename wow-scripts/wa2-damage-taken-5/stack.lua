(function()
  local gStore = aura_env

  return function(xs, ...)
    return gStore.damageTakenInTheLast5Seconds
  end
end)()
