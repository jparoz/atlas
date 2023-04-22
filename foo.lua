function add(a, b)
    return a + b + some_global
end

local foo
if USE_STRING then
    foo = "string"
else
    foo = 123
end

local first, second = ...

local foo = first + 22
local bar = second .. " and then some more stuff"

print(foo, bar)

function Foobar(a)
    local b = a
    local res = b + 1 + 2
    return res
end

local either = true and 123 or "hi"
