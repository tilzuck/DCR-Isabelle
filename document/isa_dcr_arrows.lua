-- Typesets the DCR relation arrows of the theories with the inline symbols of
-- the dcrgraph package.
--
-- Isabelle writes each arrow as a sequence of symbol tokens, e.g. the condition
-- arrow \<rightarrow>\<bullet> as {\isasymrightarrow}{\isasymbullet}. Every line
-- LuaLaTeX reads is searched for these sequences, and each is replaced by a
-- macro defined in root.tex, before TeX sees the line. The theory sources keep
-- their plain Isabelle syntax.

local arrows = {
  { "{\\isasymrightarrow}{\\isasymbullet}",   "{\\isadcrcondition}" },
  { "{\\isasymbullet}{\\isasymrightarrow}",   "{\\isadcrresponse}" },
  { "{\\isasymrightarrow}{\\isacharplus}",    "{\\isadcrinclude}" },
  { "{\\isasymrightarrow}{\\isacharpercent}", "{\\isadcrexclude}" },
}

-- Replace every occurrence of the literal string old (no Lua patterns).
local function replace_all(line, old, new)
  local parts, i = {}, 1
  while true do
    local s, e = line:find(old, i, true)
    if not s then break end
    parts[#parts + 1] = line:sub(i, s - 1)
    parts[#parts + 1] = new
    i = e + 1
  end
  parts[#parts + 1] = line:sub(i)
  return table.concat(parts)
end

luatexbase.add_to_callback("process_input_buffer", function(line)
  for _, a in ipairs(arrows) do
    line = replace_all(line, a[1], a[2])
  end
  return line
end, "isa_dcr_arrows")
