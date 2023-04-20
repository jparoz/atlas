-- constraints (input), possibilities (output)

-- {}, {}

local foo = 123

-- {}, {foo: [number]}

function bar(a, b)
    -- {a: [], b: []}, {foo: [number]}

    local c = a + 3
    -- {a: [number], b: []}, {foo: [number], c: [number]}

    local firstAlpha = b >= "azzzzzz"
    -- {a: [number], b: [string]}, {foo: [number], c: [number], firstAlpha: [bool]}

    c = true
    -- {a: [number], b: [string]}, {foo: [number], c: [boolean], firstAlpha: [bool]}

    if firstAlpha then
        c = 1234
        -- {a: [number], b: [string]}, {foo: [number], c: [number], firstAlpha: [bool]}
    else
        c = "words"
        -- {a: [number], b: [string]}, {foo: [number], c: [string], firstAlpha: [bool]}
    end
    -- {a: [number], b: [string]}, {foo: [number], c: [number, string], firstAlpha: [bool]}

    local d
    -- {a: [number], b: [string]}, {foo: [number], c: [number, string], firstAlpha: [bool], d: []}

    if firstAlpha then
        d = a
        -- {a: [number], b: [string]}, {foo: [number], c: [number, string], firstAlpha: [bool], d: [number]}
    else
        d = b
        -- {a: [number], b: [string]}, {foo: [number], c: [number, string], firstAlpha: [bool], d: [string]}
    end
    -- {a: [number], b: [string]}, {foo: [number], c: [number, string], firstAlpha: [bool], d: [number, string]}
end
-- bar: ((number, string) -> nil)


function weird(x)
    -- {x: []}, {}
    local first = x + 3
    -- {x: [number]}, {first: [number]}
    local second = x .. "foo"
    -- {x: [number, string]}, {first: [number], second: [string]}
    return x
end
-- weird: ((number & string) -> number & string)

function either(y)
    -- {y: []}, {}
    local out
    -- {y: []}, {out: []}
    if type(y) == "number" then
        -- {y: [number]}, {out: []}
        out = "banana"
        -- {y: [number]}, {out: [string]}
    elseif type(y) == "string" then
        -- {y: [string]}, {out: []}
        out = 123
        -- {y: [string]}, {out: [number]}
    end
    -- {y: [number, string]}, {out: [string, number]}
    return out
end
-- either: ((number | string) -> number | string)
