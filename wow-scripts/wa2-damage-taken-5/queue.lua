local kInitialIx = 1

local function entryCount(t)
  local s = 0
  for _ in pairs(t) do s = s + 1 end
  return s
end

-- Maybe we should use a fixed-size ring buffer for better locality
-- and less allocation...
local function create()
  local function nextIx(ix)
    return ix + 1
  end

  return {
    nextLeftIx = kInitialIx,
    rightIx = kInitialIx,
    storage = {},

    storageUsage = function(self)
      return entryCount(self.storage)
    end,

    isEmpty = function(self)
      return self.rightIx >= self.nextLeftIx
    end,

    appendLeft = function(self, x)
      local ix = self.nextLeftIx
      self.nextLeftIx = nextIx(ix)
      self.storage[ix] = x
    end,

    peek = function(self)
      return self.storage[self.rightIx]
    end,

    pop = function(self)
      local x = self:peek()
      if not self:isEmpty() then
        local ix = self.rightIx
        -- | This seems to be the standard way to remove keys from tables.
        self.storage[ix] = nil
        self.rightIx = nextIx(ix)
      end
      return x
    end,

    popWhile = function(self, predicate)
      local xs = {}
      while not self:isEmpty() do
        local x = self:peek()
        if not predicate(x) then
          break
        end
        table.insert(xs, x)
        self:pop()
      end
      return xs
    end,

    -- | This is surely slower than for loops.
    foldr = function(self, combine, init)
      for ix = self.rightIx, self.nextLeftIx - 1 do
        init = combine(self.storage[ix], init)
      end
      return init
    end,
  }
end

return {
  create = create,
}

