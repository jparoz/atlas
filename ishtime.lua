function add(a, b)
    return a + b + some_global
end

local foo
if USE_STRING then
    foo = "string"
else
    foo = 123
end

local hours = {
    [0] = "twelve",
    "one",
    "two",
    "three",
    "four",
    "five",
    "six",
    "seven",
    "eight",
    "nine",
    "ten",
    "eleven",
}

local minutes = {
    "five past",
    "ten past",
    "a quarter past",
    "twenty past",
    "twenty-five past",
    "half past",
    "twenty-five to",
    "twenty to",
    "a quarter to",
    "ten to",
    "five to",
}

local function ishtime(time)
    local min, hour = time.min, time.hour % 12

    if min <= 2 or min >= 57 then
        return ("It's %s o'clock."):format(hours[hour])
    else
        return ("It's %s %s."):format(minutes[((min-3) // 5) + 1],
                                      hours[(hour) + (min // 33)])
    end
end

io.write(ishtime(os.date("*t")));

if arg[1] ~= "-n" then
    io.write("\n")
end

return ishtime
