function third(...)
  local _, _, res = ...
  return res
end
assert(third(1, 2, 3) == 3)

function third1(...)
  -- We can pass varargs to another function directly.
  return third(...)
end
assert(third1(1, 2, 3) == 3)

function third2(...)
  return select(3, ...)
end
assert(third2(1, 2, 3) == 3)

-- Can't do this as the vararg expression must be used immediately in the
-- containing function.
-- This is somehow expected since varargs are in the immediate callee's stack
-- and could not be cheaply passed as upvals.
function third3(...)
  return (function()
    return select(3, ...)
  end)()
end
