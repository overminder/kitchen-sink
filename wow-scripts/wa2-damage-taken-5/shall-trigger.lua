(function()
  -- ^ Since WA requires an expression in its textarea.

  -- | Yeah, CPP is a good idea.
  local queue = (function()
    #include "queue.lua"
  end)()

  local kSecondsToStale = 5

  -- | aura_env seems to be the standard way to do
  -- inter-textarea communication.
  local gStore = aura_env

  local damages = queue.create()

  local playerGUID = UnitGUID("player")

  local function createDamageHandler(offset)
    if offset == nil then
      offset = 0
    end
    return function(...)
      local amount = select(12 + offset, ...)
      local absorbed = select(17 + offset, ...)
      if absorbed == nil then
        absorbed = 0
      end
      damages:appendLeft({time(), amount + absorbed})
    end
  end

  local handleSwingDamage = createDamageHandler()
  local handleSpellDamage = createDamageHandler(3)

  local function damageTakenInTheLast5Seconds()
    local now = time()
    local becameStale = now - kSecondsToStale
    damages:popWhile(function(tv)
      local t, _ = unpack(tv)
      return t < becameStale
    end)
    return damages:foldr(function(tv, acc)
      local _, v = unpack(tv)
      return acc + v
    end, 0)
  end

  -- Mostly from FrenzyRegen (https://mods.curse.com/addons/wow/frenzyregen)
  -- We could also take a look at https://mods.curse.com/addons/wow/blood-shield-tracker.
  local interestedEventTypes = {
    SWING_DAMAGE = handleSwingDamage,
    SPELL_DAMAGE = handleSpellDamage,
    SPELL_PERIODIC_DAMAGE = handleSpellDamage,
    RANGE_DAMAGE = handleSpellDamage,
  }

  return function(event, ...)
    local spec = GetSpecialization()
    local role = GetSpecializationRole(spec)
    if role ~= 'TANK' then
      return false
    end

    local _, eventType, _, _, _, _, _, destGUID = ...
    if destGUID ~= playerGUID then
      return false
    end

    local lookInside = interestedEventTypes[eventType]
    if lookInside then
      lookInside(...)
      gStore.damageTakenInTheLast5Seconds = damageTakenInTheLast5Seconds()
    end
    return lookInside
  end
end)()
