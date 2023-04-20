local first, second = ...

local foo = first + 22
local bar = second .. " and then some more stuff"

print(foo, bar)

function Foobar(a)
    local b = a
    local res = b + 1
    return res
end
