package.preload['moonscript.parse'] = function()
  module("moonscript.parse", package.seeall)
  
  local util = require"moonscript.util"
  
  require"lpeg"
  
  local dump = require"moonscript.dump"
  local data = require"moonscript.data"
  
  local ntype = data.ntype
  local trim = util.trim
  
  local Stack = data.Stack
  
  local function count_indent(str)
  	local sum = 0
  	for v in str:gmatch("[\t ]") do
  		if v == ' ' then sum = sum + 1 end
  		if v == '\t' then sum = sum + 4 end
  	end
  	return sum
  end
  
  local R, S, V, P = lpeg.R, lpeg.S, lpeg.V, lpeg.P
  local C, Ct, Cmt, Cg, Cb, Cc = lpeg.C, lpeg.Ct, lpeg.Cmt, lpeg.Cg, lpeg.Cb, lpeg.Cc
  
  lpeg.setmaxstack(3000)
  
  local White = S" \t\n"^0
  local _Space = S" \t"^0
  local Break = P"\n"
  local Stop = Break + -1
  local Indent = C(S"\t "^0) / count_indent
  
  local Comment = P"--" * (1 - S"\n")^0 * #Stop
  local Space = _Space * Comment^-1
  local SomeSpace = S" \t"^1 * Comment^-1
  
  local SpaceBreak = Space * Break
  local EmptyLine = SpaceBreak
  
  local _Name = C(R("az", "AZ", "__") * R("az", "AZ", "09", "__")^0)
  local Name = Space * _Name
  
  local Num = P"0x" * R("09", "af", "AF")^1 +
  	R"09"^1 * (P"." * R"09"^1)^-1 * (S"eE" * P"-"^-1 * R"09"^1)^-1
  
  Num = Space * (Num / function(value) return {"number", value} end)
  
  local FactorOp = Space * C(S"+-")
  local TermOp = Space * C(S"*/%^")
  
  local Shebang = P"#!" * P(1 - Stop)^0
  
  local function wrap(fn)
  	local env = getfenv(fn)
  
  	return setfenv(fn, setmetatable({}, {
  		__index = function(self, name)
  			local value = env[name] 
  			if value ~= nil then return value end
  
  			if name:match"^[A-Z][A-Za-z0-9]*$" then
  				local v = V(name)
  				rawset(self, name, v)
  				return v
  			end
  			error("unknown variable referenced: "..name)
  		end
  	}))
  end
  
  function extract_line(str, start_pos)
  	str = str:sub(start_pos)
  	m = str:match"^(.-)\n"
  	if m then return m end
  	return str:match"^.-$"
  end
  
  local function mark(name)
  	return function(...)
  		return {name, ...}
  	end
  end
  
  local function insert_pos(pos, value)
      if type(value) == "table" then
          value[-1] = pos
      end
      return value
  end
  
  local function pos(patt)
  	return (lpeg.Cp() * patt) / insert_pos
  end
  
  local function got(what)
  	return Cmt("", function(str, pos, ...)
  		local cap = {...}
  		print("++ got "..what, "["..extract_line(str, pos).."]")
  		return true
  	end)
  end
  
  local function flatten(tbl)
  	if #tbl == 1 then
  		return tbl[1]
  	end
  	return tbl
  end
  
  local function flatten_or_mark(name)
  	return function(tbl)
  		if #tbl == 1 then return tbl[1] end
  		table.insert(tbl, 1, name)
  		return tbl
  	end
  end
  
  local build_grammar = wrap(function()
  	local err_msg = "Failed to parse:\n [%d] >>    %s (%d)"
  
  	local _indent = Stack(0) -- current indent
  
  	local last_pos = 0 -- used to know where to report error
  	local function check_indent(str, pos, indent)
  		last_pos = pos
  		return _indent:top() == indent
  	end
  
  	local function advance_indent(str, pos, indent)
  		if indent > _indent:top() then
  			_indent:push(indent)
  			return true
  		end
  	end
  
  	local function push_indent(str, pos, indent)
  		_indent:push(indent)
  		return true
  	end
  
  	local function pop_indent(str, pos)
  		if not _indent:pop() then error("unexpected outdent") end
  		return true
  	end
  
  	local keywords = {}
  	local function key(word)
  		keywords[word] = true
  		return Space * word
  	end
  
  	local function op(word)
  		if word:match("^%w*$") then
  			keywords[word] = true
  		end
  		return Space * C(word)
  	end
  
  	local function sym(chars)
  		return Space * chars
  	end
  
  	local function symx(chars)
  		return chars
  	end
  
  	local function flatten_func(callee, args)
  		if #args == 0 then return callee end
  
  		args = {"call", args}
  		if ntype(callee) == "chain" then
  			-- check for colon stub that needs arguments
  			if ntype(callee[#callee]) == "colon_stub" then
  				local stub = callee[#callee]
  				stub[1] = "colon"
  				table.insert(stub, args)
  			else
  				table.insert(callee, args)
  			end
  
  			return callee
  		end
  
  		return {"chain", callee, args}
  	end
  
  	local function wrap_func_arg(value)
  		return {"call", {value}}
  	end
  
  	-- makes sure the last item in a chain is an index
  	local _assignable = { index = true, dot = true, slice = true }
  	local function check_assignable(str, pos, value)
  		if ntype(value) == "chain" and _assignable[ntype(value[#value])]
  			or type(value) == "string"
  		then
  			return true, value
  		end
  		return false
  	end
  
  	local SimpleName = Name -- for table key
  
  	-- make sure name is not a keyword
  	local Name = Cmt(Name, function(str, pos, name)
  		if keywords[name] then return false end
  		return true
  	end) / trim
  
  	local Name = sym"@" * Name / mark"self" + Name + Space * "..." / trim
  
  	local function simple_string(delim, x)
  		return C(symx(delim)) * C((P('\\'..delim) + (1 - S('\n'..delim)))^0) * sym(delim) / mark"string"
  	end
  
  	-- wrap if statement if there is a conditional decorator
  	local function wrap_if(stm, cond)
  		if cond then
  			local pass, fail = unpack(cond)
  			if fail then fail = {"else", {fail}} end
  			return {"if", cond[2], {stm}, fail}
  		end
  		return stm
  	end
  
  	local function wrap_decorator(stm, dec)
  		if not dec then return stm end
  
  		local arg = {stm, dec}
  
  		if dec[1] == "if" then
  			local _, cond, fail = unpack(dec)
  			if fail then fail = {"else", {fail}} end
  			stm = {"if", cond, {stm}, fail}
  		elseif dec[1] == "comprehension" then
  			local _, clauses = unpack(dec)
  			stm = {"comprehension", stm, clauses}
  		end
  
  		return stm
  	end
  
  	local function wrap_default_arg(name, default)
  		if not default then return name end
  		return {name, default}
  	end
  
  	local function check_lua_string(str, pos, right, left)
  		return #left == #right
  	end
  
  	-- :name in table literal
  	local function self_assign(name)
  		return {name, name}
  	end
  
  	-- can't have P(false) because it causes preceding patterns not to run
  	local Cut = P(function() return false end)
  
  	local g = lpeg.P{
  		File,
  		File = Shebang^-1 * (Block + Ct""),
  		Block = Ct(Line * (Break^1 * Line)^0),
  		CheckIndent = Cmt(Indent, check_indent), -- validates line is in correct indent
  		Line = CheckIndent * Statement + Space * #Break,
  
  		Statement = (Import + While + With + For + ForEach + Return
  			+ ClassDecl + Export + BreakLoop + Ct(ExpList) / flatten_or_mark"explist" * Space) * ((
  				-- statement decorators
  				key"if" * Exp * (key"else" * Exp)^-1 * Space / mark"if" +
  				CompInner / mark"comprehension"
  			) * Space)^-1 / wrap_decorator,
  
  		Body = Space^-1 * Break * EmptyLine^0 * InBlock + Ct(Statement), -- either a statement, or an indented block
  
  		Advance = #Cmt(Indent, advance_indent), -- Advances the indent, gives back whitespace for CheckIndent
  		PushIndent = Cmt(Indent, push_indent),
  		PopIndent = Cmt("", pop_indent),
  		InBlock = Advance * Block * PopIndent,
  
  		Import = key"import" *  Ct(ImportNameList) * key"from" * Exp / mark"import", 
  		ImportName = (sym"\\" * Ct(Cc":" * Name) + Name),
  		ImportNameList = ImportName * (sym"," * ImportName)^0,
  
  		NameList = Name * (sym"," * Name)^0,
  
  		BreakLoop = Ct(key"break"/trim),
  
  		Return = key"return" * (ExpListLow/ mark"explist") / mark"return",
  
  		With = key"with" * Exp * key"do"^-1 * Body / mark"with",
  
  		If = key"if" * Exp * key"then"^-1 * Body *
  			((Break * CheckIndent)^-1 * EmptyLine^0 * key"elseif" * Exp * key"then"^-1 * Body / mark"elseif")^0 *
  			((Break * CheckIndent)^-1 * EmptyLine^0 * key"else" * Body / mark"else")^-1 / mark"if",
  
  		While = key"while" * Exp * key"do"^-1 * Body / mark"while",
  
  		For = key"for" * (Name * sym"=" * Ct(Exp * sym"," * Exp * (sym"," * Exp)^-1)) *
  			key"do"^-1 * Body / mark"for",
  
  		ForEach = key"for" * Ct(NameList) * key"in" * (sym"*" * Exp / mark"unpack" + Exp) * key"do"^-1 * Body / mark"foreach",
  
  		Comprehension = sym"[" * Exp * CompInner * sym"]" / mark"comprehension",
  
  		CompInner = Ct(CompFor * CompClause^0),
  		CompFor = key"for" * Ct(NameList) * key"in" * (sym"*" * Exp / mark"unpack" + Exp) / mark"for",
  		CompClause = CompFor + key"when" * Exp / mark"when",
  
  		Assign = Ct(AssignableList) * sym"=" * (With + If + Ct(TableBlock + ExpListLow)) / mark"assign",
  		Update = Assignable * ((sym"..=" + sym"+=" + sym"-=" + sym"*=" + sym"/=" + sym"%=")/trim) * Exp / mark"update",
  
  		-- we can ignore precedence for now
  		OtherOps = op"or" + op"and" + op"<=" + op">=" + op"~=" + op"!=" + op"==" + op".." + op"<" + op">",
  
  		Assignable = Cmt(DotChain + Chain, check_assignable) + Name,
  		AssignableList = Assignable * (sym"," * Assignable)^0,
  
  		Exp = Ct(Value * ((OtherOps + FactorOp + TermOp) * Value)^0) / flatten_or_mark"exp",
  
  		-- Exp = Ct(Factor * (OtherOps * Factor)^0) / flatten_or_mark"exp",
  		-- Factor = Ct(Term * (FactorOp * Term)^0) / flatten_or_mark"exp",
  		-- Term = Ct(Value * (TermOp * Value)^0) / flatten_or_mark"exp",
  
  		SimpleValue =
  			If +
  			With +
  			ForEach + For + While +
  			sym"-" * -SomeSpace * Exp / mark"minus" +
  			sym"#" * Exp / mark"length" +
  			sym"not" * Exp / mark"not" +
  			TableLit +
  			Comprehension +
  			Assign + Update + FunLit + String +
  			Num,
  
  		ChainValue = -- a function call or an object access
  			((Chain + DotChain + Callable) * Ct(InvokeArgs^-1)) / flatten_func,
  
  		Value = pos(
  			SimpleValue +
  			Ct(KeyValueList) / mark"table" +
  			ChainValue),
  
  		SliceValue = SimpleValue + ChainValue,
  
  		String = Space * DoubleString + Space * SingleString + LuaString,
  		SingleString = simple_string("'"),
  		DoubleString = simple_string('"'),
  
  		LuaString = Cg(LuaStringOpen, "string_open") * Cb"string_open" * P"\n"^-1 *
  			C((1 - Cmt(C(LuaStringClose) * Cb"string_open", check_lua_string))^0) *
  			C(LuaStringClose) / mark"string",
  
  		LuaStringOpen = sym"[" * P"="^0 * "[" / trim,
  		LuaStringClose = "]" * P"="^0 * "]",
  
  		Callable = Name + Parens / mark"parens",
  		Parens = sym"(" * Exp * sym")",
  
  		FnArgs = symx"(" * Ct(ExpList^-1) * sym")" + sym"!" * -P"=" * Ct"",
  
  		-- a list of funcalls and indexs on a callable
  		Chain = Callable * (ChainItem^1 * ColonSuffix^-1 + ColonSuffix) / mark"chain",
  
  		-- shorthand dot call for use in with statement
  		DotChain =
  			(sym"." * Cc(-1) * (_Name / mark"dot") * ChainItem^0) / mark"chain" + 
  			(sym"\\" * Cc(-1) * (
  				(_Name * Invoke / mark"colon") * ChainItem^0 + 
  				(_Name / mark"colon_stub")
  			)) / mark"chain",
  
  		ChainItem = 
  			Invoke + 
  			Slice +
  			symx"[" * Exp/mark"index" * sym"]" +
  			symx"." * _Name/mark"dot" +
  			ColonCall,
  
  		Slice = symx"[" * (SliceValue + Cc(1)) * sym":" * (SliceValue + Cc"")  *
  			(sym":" * SliceValue)^-1 *sym"]" / mark"slice",
  
  		ColonCall = symx"\\" * (_Name * Invoke) / mark"colon",
  		ColonSuffix = symx"\\" * _Name / mark"colon_stub",
  
  		Invoke = FnArgs/mark"call" +
  			SingleString / wrap_func_arg +
  			DoubleString / wrap_func_arg,
  
  		TableValue = KeyValue + Ct(Exp),
  
  		TableLit = sym"{" * Ct(
  				TableValueList^-1 * sym","^-1 *
  				(SpaceBreak * TableLitLine * (sym","^-1 * SpaceBreak * TableLitLine)^0 * sym","^-1)^-1
  			) * White * sym"}" / mark"table",
  
  		TableValueList = TableValue * (sym"," * TableValue)^0,
  		TableLitLine = PushIndent * ((TableValueList * PopIndent) + (PopIndent * Cut)) + Space,
  
  		-- the unbounded table
  		TableBlockInner = Ct(KeyValueLine * (SpaceBreak^1 * KeyValueLine)^0),
  		TableBlock = SpaceBreak^1 * Advance * TableBlockInner * PopIndent / mark"table",
  
  		ClassDecl = key"class" * Name * (key"extends" * Exp + C"")^-1 * TableBlock / mark"class",
  		Export = key"export" * Ct(NameList) / mark"export",
  
  		KeyValue = (sym":" * Name) / self_assign + Ct((SimpleName + sym"[" * Exp * sym"]") * symx":" * (Exp + TableBlock)),
  		KeyValueList = KeyValue * (sym"," * KeyValue)^0,
  		KeyValueLine = CheckIndent * KeyValueList * sym","^-1,
  
  		FnArgsDef = sym"(" * Ct(FnArgDefList^-1) *
  			(key"using" * Ct(NameList + Space * "nil") + Ct"") *
  			sym")" + Ct"" * Ct"",
  
  		FnArgDefList =  FnArgDef * (sym"," * FnArgDef)^0,
  		FnArgDef = Name * (sym"=" * Exp)^-1 / wrap_default_arg,
  
  		FunLit = FnArgsDef *
  			(sym"->" * Cc"slim" + sym"=>" * Cc"fat") *
  			(Body + Ct"") / mark"fndef",
  
  		NameList = Name * (sym"," * Name)^0,
  		ExpList = Exp * (sym"," * Exp)^0,
  		ExpListLow = Exp * ((sym"," + sym";") * Exp)^0,
  
  		InvokeArgs = ExpList * (sym"," * SpaceBreak * Advance * ArgBlock)^-1,
  		ArgBlock = ArgLine * (sym"," * SpaceBreak * ArgLine)^0 * PopIndent,
  		ArgLine = CheckIndent * ExpList
  	}
  
  	return {
  		_g = White * g * White * -1,
  		match = function(self, str, ...)
  
  			local pos_to_line = function(pos)
  				return util.pos_to_line(str, pos)
  			end
  
  			local get_line = function(num)
  				return util.get_line(str, num)
  			end
  
  			local tree
  			local args = {...}
  			local pass, err = pcall(function()
  				tree = self._g:match(str, unpack(args))
  			end)
  
  			if not pass then
  				local line_no = pos_to_line(last_pos)
  				print("stopped at", line_no)
  				error(err)
  			end
  
  			if not tree then
  				local line_no = pos_to_line(last_pos)
  				local line_str = get_line(line_no) or ""
  				
  				return nil, err_msg:format(line_no, trim(line_str), _indent:top())
  			end
  			return tree
  		end
  	}
  	
  end)
  
  -- parse a string
  -- returns tree, or nil and error message
  function string(str)
  	local g = build_grammar()
  	return g:match(str)
  end
  
  
end
package.preload['moonscript.util'] = function()
  module("moonscript.util", package.seeall)
  local concat = table.concat
  moon = {
    is_object = function(value)
      return type(value) == "table" and value.__class
    end,
    type = function(value)
      local base_type = type(value)
      if base_type == "table" then
        local cls = value.__class
        if cls then
          return cls
        end
      end
      return base_type
    end
  }
  pos_to_line = function(str, pos)
    local line = 1
    for _ in str:sub(1, pos):gmatch("\n") do
      line = line + 1
    end
    return line
  end
  get_closest_line = function(str, line_num)
    local line = get_line(str, line_num)
    if (not line or trim(line) == "") and line_num > 1 then
      return get_closest_line(str, line_num - 1)
    else
      return line, line_num
    end
  end
  get_line = function(str, line_num)
    for line in str:gmatch("(.-)[\n$]") do
      if line_num == 1 then
        return line
      end
      line_num = line_num - 1
    end
  end
  reversed = function(seq)
    return coroutine.wrap(function()
      for i = #seq, 1, -1 do
        coroutine.yield(i, seq[i])
      end
    end)
  end
  trim = function(str)
    return str:match("^%s*(.-)%s*$")
  end
  split = function(str, delim)
    if str == "" then
      return { }
    end
    str = str .. delim
    return (function()
      local _accum_0 = { }
      local _len_0 = 0
      for m in str:gmatch("(.-)" .. delim) do
        _len_0 = _len_0 + 1
        _accum_0[_len_0] = m
      end
      return _accum_0
    end)()
  end
  dump = function(what)
    local seen = { }
    local _dump
    _dump = function(what, depth)
      if depth == nil then
        depth = 0
      end
      local t = type(what)
      if t == "string" then
        return '"' .. what .. '"\n'
      elseif t == "table" then
        if seen[what] then
          return "recursion(" .. tostring(what) .. ")...\n"
        end
        local _ = seen[what] == true
        depth = depth + 1
        local lines = (function()
          local _accum_0 = { }
          local _len_0 = 0
          for k, v in pairs(what) do
            local _value_0 = (" "):rep(depth * 4) .. "[" .. tostring(k) .. "] = " .. _dump(v, depth)
            if _value_0 ~= nil then
              _len_0 = _len_0 + 1
              _accum_0[_len_0] = _value_0
            end
          end
          return _accum_0
        end)()
        seen[what] = false
        return "{\n" .. concat(lines) .. (" "):rep((depth - 1) * 4) .. "}\n"
      else
        return tostring(what) .. "\n"
      end
    end
    return _dump(what)
  end
  
end
package.preload['moonscript.data'] = function()
  module("moonscript.data", package.seeall)
  local concat = table.concat
  ntype = function(node)
    if type(node) ~= "table" then
      return "value"
    else
      return node[1]
    end
  end
  Set = function(items)
    local self = { }
    do
      local _item_0 = items
      for _index_0 = 1, #_item_0 do
        local key = _item_0[_index_0]
        self[key] = true
      end
    end
    return self
  end
  Stack = (function(_parent_0)
    local _base_0 = {
      __tostring = function(self)
        return "<Stack {" .. concat(self, ", ") .. "}>"
      end,
      pop = function(self)
        return table.remove(self)
      end,
      push = function(self, value)
        table.insert(self, value)
        return value
      end,
      top = function(self)
        return self[#self]
      end
    }
    _base_0.__index = _base_0
    if _parent_0 then
      setmetatable(_base_0, getmetatable(_parent_0).__index)
    end
    local _class_0 = setmetatable({
      __init = function(self, ...)
        do
          local _item_0 = {
            ...
          }
          for _index_0 = 1, #_item_0 do
            local v = _item_0[_index_0]
            self:push(v)
          end
        end
        return nil
      end
    }, {
      __index = _base_0,
      __call = function(mt, ...)
        local self = setmetatable({}, _base_0)
        mt.__init(self, ...)
        return self
      end
    })
    _base_0.__class = _class_0
    return _class_0
  end)()
  lua_keywords = Set({
    'and',
    'break',
    'do',
    'else',
    'elseif',
    'end',
    'false',
    'for',
    'function',
    'if',
    'in',
    'local',
    'nil',
    'not',
    'or',
    'repeat',
    'return',
    'then',
    'true',
    'until',
    'while'
  })
  
end
package.preload['moonscript'] = function()
  module("moonscript", package.seeall)
  require("moonscript.parse")
  require("moonscript.compile")
  require("moonscript.util")
  local concat, insert = table.concat, table.insert
  local split, dump = util.split, util.dump
  dirsep = "/"
  line_tables = { }
  local create_moonpath
  create_moonpath = function(package_path)
    local paths = split(package_path, ";")
    for i, path in ipairs(paths) do
      local p = path:match("^(.-)%.lua$")
      if p then
        paths[i] = p .. ".moon"
      end
    end
    return concat(paths, ";")
  end
  moon_chunk = function(file, file_path)
    local text = file:read("*a")
    if not text then
      error("Could not read file")
    end
    local tree, err = parse.string(text)
    if not tree then
      error("Parse error: " .. err)
    end
    local code, ltable, pos = compile.tree(tree)
    if not code then
      error(compile.format_error(ltable, pos, text))
    end
    line_tables[file_path] = ltable
    local runner
    runner = function()
      do
        local _with_0 = code
        code = nil
        return _with_0
      end
    end
    return load(runner, file_path)
  end
  moon_loader = function(name)
    local name_path = name:gsub("%.", dirsep)
    local file, file_path = nil, nil
    do
      local _item_0 = split(package.moonpath, ";")
      for _index_0 = 1, #_item_0 do
        local path = _item_0[_index_0]
        file_path = path:gsub("?", name_path)
        file = io.open(file_path)
        if file then
          break
        end
      end
    end
    if file then
      return moon_chunk(file, file_path)
    else
      return nil, "Could not find moon file"
    end
  end
  if not package.moonpath then
    package.moonpath = create_moonpath(package.path)
  end
  local init_loader
  init_loader = function()
    return insert(package.loaders, 2, moon_loader)
  end
  if not _G.moon_no_loader then
    init_loader()
  end
  
end
package.preload['moonscript.compile'] = function()
  module("moonscript.compile", package.seeall)
  local util = require("moonscript.util")
  local data = require("moonscript.data")
  local dump = require("moonscript.dump")
  require("moonscript.compile.format")
  require("moonscript.compile.line")
  require("moonscript.compile.value")
  local ntype, Set = data.ntype, data.Set
  local concat, insert = table.concat, table.insert
  local pos_to_line, get_closest_line, trim = util.pos_to_line, util.get_closest_line, util.trim
  local bubble_names = {
    "has_varargs"
  }
  local Line
  Line = (function(_parent_0)
    local _base_0 = {
      _append_single = function(self, item)
        if util.moon.type(item) == Line then
          do
            local _item_0 = item
            for _index_0 = 1, #_item_0 do
              local value = _item_0[_index_0]
              self:_append_single(value)
            end
          end
        else
          insert(self, item)
        end
        return nil
      end,
      append_list = function(self, items, delim)
        for i = 1, #items do
          self:_append_single(items[i])
          if i < #items then
            insert(self, delim)
          end
        end
      end,
      append = function(self, ...)
        do
          local _item_0 = {
            ...
          }
          for _index_0 = 1, #_item_0 do
            local item = _item_0[_index_0]
            self:_append_single(item)
          end
        end
        return nil
      end,
      render = function(self)
        local buff = { }
        for i = 1, #self do
          local c = self[i]
          insert(buff, (function()
            if util.moon.type(c) == Block then
              return c:render()
            else
              return c
            end
          end)())
        end
        return concat(buff)
      end
    }
    _base_0.__index = _base_0
    if _parent_0 then
      setmetatable(_base_0, getmetatable(_parent_0).__index)
    end
    local _class_0 = setmetatable({
      __init = function(self, ...)
        if _parent_0 then
          return _parent_0.__init(self, ...)
        end
      end
    }, {
      __index = _base_0,
      __call = function(mt, ...)
        local self = setmetatable({}, _base_0)
        mt.__init(self, ...)
        return self
      end
    })
    _base_0.__class = _class_0
    return _class_0
  end)()
  local Block_
  Block_ = (function(_parent_0)
    local _base_0 = {
      header = "do",
      footer = "end",
      line_table = function(self)
        return self._posmap
      end,
      set = function(self, name, value)
        self._state[name] = value
      end,
      get = function(self, name)
        return self._state[name]
      end,
      declare = function(self, names)
        local undeclared = (function()
          local _accum_0 = { }
          local _len_0 = 0
          do
            local _item_0 = names
            for _index_0 = 1, #_item_0 do
              local name = _item_0[_index_0]
              if type(name) == "string" and not self:has_name(name) then
                _len_0 = _len_0 + 1
                _accum_0[_len_0] = name
              end
            end
          end
          return _accum_0
        end)()
        do
          local _item_0 = undeclared
          for _index_0 = 1, #_item_0 do
            local name = _item_0[_index_0]
            self:put_name(name)
          end
        end
        return undeclared
      end,
      whitelist_names = function(self, names)
        self._name_whitelist = Set(names)
      end,
      put_name = function(self, name)
        self._names[name] = true
      end,
      has_name = function(self, name)
        local yes = self._names[name]
        if yes == nil and self.parent then
          if not self._name_whitelist or self._name_whitelist[name] then
            return self.parent:has_name(name)
          end
        else
          return yes
        end
      end,
      shadow_name = function(self, name)
        self._names[name] = false
      end,
      free_name = function(self, prefix, dont_put)
        prefix = prefix or "moon"
        local searching = true
        local name, i = nil, 0
        while searching do
          name = concat({
            "",
            prefix,
            i
          }, "_")
          i = i + 1
          searching = self:has_name(name)
        end
        if not dont_put then
          self:put_name(name)
        end
        return name
      end,
      init_free_var = function(self, prefix, value)
        local name = self:free_name(prefix, true)
        self:stm({
          "assign",
          {
            name
          },
          {
            value
          }
        })
        return name
      end,
      mark_pos = function(self, node)
        if node[-1] then
          self.last_pos = node[-1]
          if not self._posmap[self.current_line] then
            self._posmap[self.current_line] = self.last_pos
          end
        end
      end,
      add_line_text = function(self, text)
        return insert(self._lines, text)
      end,
      append_line_table = function(self, sub_table, offset)
        offset = offset + self.current_line
        for line, source in pairs(sub_table) do
          local line = line + offset
          if not self._posmap[line] then
            self._posmap[line] = source
          end
        end
      end,
      add_line_tables = function(self, line)
        do
          local _item_0 = line
          for _index_0 = 1, #_item_0 do
            local chunk = _item_0[_index_0]
            if util.moon.type(chunk) == Block then
              local current = chunk
              while current do
                if util.moon.type(current.header) == Line then
                  self:add_line_tables(current.header)
                end
                self:append_line_table(current:line_table(), 0)
                self.current_line = self.current_line + current.current_line
                current = current.next
              end
            end
          end
        end
      end,
      add = function(self, line)
        local t = util.moon.type(line)
        if t == "string" then
          self:add_line_text(line)
        elseif t == Block then
          do
            local _item_0 = bubble_names
            for _index_0 = 1, #_item_0 do
              local name = _item_0[_index_0]
              if line[name] then
                self[name] = line.name
              end
            end
          end
          self:add(self:line(line))
        elseif t == Line then
          self:add_line_tables(line)
          self:add_line_text(line:render())
          self.current_line = self.current_line + 1
        else
          error("Adding unknown item")
        end
        return nil
      end,
      _insert_breaks = function(self)
        for i = 1, #self._lines - 1 do
          local left, right = self._lines[i], self._lines[i + 1]
          if left:sub(-1) == ")" and right:sub(1, 1) == "(" then
            self._lines[i] = self._lines[i] .. ";"
          end
        end
      end,
      render = function(self)
        local flatten
        flatten = function(line)
          if type(line) == "string" then
            return line
          else
            return line:render()
          end
        end
        local header = flatten(self.header)
        if #self._lines == 0 then
          local footer = flatten(self.footer)
          return concat({
            header,
            footer
          }, " ")
        end
        local indent = indent_char:rep(self.indent)
        if not self.delim then
          self:_insert_breaks()
        end
        local body = indent .. concat(self._lines, (self.delim or "") .. "\n" .. indent)
        return concat({
          header,
          body,
          indent_char:rep(self.indent - 1) .. (function()
            if self.next then
              return self.next:render()
            else
              return flatten(self.footer)
            end
          end)()
        }, "\n")
      end,
      block = function(self, header, footer)
        return Block(self, header, footer)
      end,
      line = function(self, ...)
        do
          local _with_0 = Line()
          _with_0:append(...)
          return _with_0
        end
      end,
      is_stm = function(self, node)
        return line_compile[ntype(node)] ~= nil
      end,
      is_value = function(self, node)
        local t = ntype(node)
        return value_compile[t] ~= nil or t == "value"
      end,
      name = function(self, node)
        return self:value(node)
      end,
      value = function(self, node, ...)
        local action
        if type(node) ~= "table" then
          action = "raw_value"
        else
          self:mark_pos(node)
          action = node[1]
        end
        local fn = value_compile[action]
        if not fn then
          error("Failed to compile value: " .. dump.value(node))
        end
        return fn(self, node, ...)
      end,
      values = function(self, values, delim)
        delim = delim or ', '
        do
          local _with_0 = Line()
          _with_0:append_list((function()
            local _accum_0 = { }
            local _len_0 = 0
            do
              local _item_0 = values
              for _index_0 = 1, #_item_0 do
                local v = _item_0[_index_0]
                _len_0 = _len_0 + 1
                _accum_0[_len_0] = self:value(v)
              end
            end
            return _accum_0
          end)(), delim)
          return _with_0
        end
      end,
      stm = function(self, node, ...)
        local fn = line_compile[ntype(node)]
        if not fn then
          if has_value(node) then
            return self:stm({
              "assign",
              {
                "_"
              },
              {
                node
              }
            })
          else
            return self:add(self:value(node))
          end
        else
          self:mark_pos(node)
          local out = fn(self, node, ...)
          if out then
            return self:add(out)
          end
        end
      end,
      ret_stms = function(self, stms, ret)
        if not ret then
          ret = default_return
        end
        local i = 1
        while i < #stms do
          self:stm(stms[i])
          i = i + 1
        end
        local last_exp = stms[i]
        if last_exp then
          if cascading[ntype(last_exp)] then
            self:stm(last_exp, ret)
          elseif self:is_value(last_exp) then
            local line = ret(stms[i])
            if self:is_stm(line) then
              self:stm(line)
            else
              error("got a value from implicit return")
            end
          else
            self:stm(last_exp)
          end
        end
        return nil
      end,
      stms = function(self, stms, ret)
        if ret then
          self:ret_stms(stms, ret)
        else
          do
            local _item_0 = stms
            for _index_0 = 1, #_item_0 do
              local stm = _item_0[_index_0]
              self:stm(stm)
            end
          end
        end
        return nil
      end
    }
    _base_0.__index = _base_0
    if _parent_0 then
      setmetatable(_base_0, getmetatable(_parent_0).__index)
    end
    local _class_0 = setmetatable({
      __init = function(self, parent, header, footer)
        self.parent, self.header, self.footer = parent, header, footer
        self.current_line = 1
        self._lines = { }
        self._posmap = { }
        self._names = { }
        self._state = { }
        if self.parent then
          self.indent = self.parent.indent + 1
          return setmetatable(self._state, {
            __index = self.parent._state
          })
        else
          self.indent = 0
        end
      end
    }, {
      __index = _base_0,
      __call = function(mt, ...)
        local self = setmetatable({}, _base_0)
        mt.__init(self, ...)
        return self
      end
    })
    _base_0.__class = _class_0
    return _class_0
  end)()
  local RootBlock
  RootBlock = (function(_parent_0)
    local _base_0 = {
      render = function(self)
        self:_insert_breaks()
        return concat(self._lines, "\n")
      end
    }
    _base_0.__index = _base_0
    if _parent_0 then
      setmetatable(_base_0, getmetatable(_parent_0).__index)
    end
    local _class_0 = setmetatable({
      __init = function(self, ...)
        if _parent_0 then
          return _parent_0.__init(self, ...)
        end
      end
    }, {
      __index = _base_0,
      __call = function(mt, ...)
        local self = setmetatable({}, _base_0)
        mt.__init(self, ...)
        return self
      end
    })
    _base_0.__class = _class_0
    return _class_0
  end)(Block_)
  Block = Block_
  format_error = function(msg, pos, file_str)
    local line = pos_to_line(file_str, pos)
    local line_str
    line_str, line = get_closest_line(file_str, line)
    line_str = line_str or ""
    return concat({
      "Compile error: " .. msg,
      (" [%d] >>    %s"):format(line, trim(line_str))
    }, "\n")
  end
  tree = function(tree)
    local scope = RootBlock()
    local runner = coroutine.create(function()
      do
        local _item_0 = tree
        for _index_0 = 1, #_item_0 do
          local line = _item_0[_index_0]
          scope:stm(line)
        end
      end
      return scope:render()
    end)
    local success, result = coroutine.resume(runner)
    if not success then
      local error_msg
      if type(result) == "table" then
        local error_type = result[1]
        if error_type == "user-error" then
          error_msg = result[2]
        else
          error_msg = error("Unknown error thrown", util.dump(error_msg))
        end
      else
        error_msg = concat({
          result,
          debug.traceback(runner)
        }, "\n")
      end
      return nil, error_msg, scope.last_pos
    else
      local tbl = scope:line_table()
      return result, tbl
    end
  end
  
end
package.preload['moonscript.version'] = function()
  
  module("moonscript.version", package.seeall)
  
  version = "0.2.0-dev"
  function print_version()
  	print("MoonScript version "..version)
  end
  
end
package.preload['moonscript.compile.value'] = function()
  module("moonscript.compile", package.seeall)
  local util = require("moonscript.util")
  local data = require("moonscript.data")
  require("moonscript.compile.format")
  local ntype = data.ntype
  local concat, insert = table.concat, table.insert
  local table_append
  table_append = function(name, len, value)
    return {
      {
        "update",
        len,
        "+=",
        1
      },
      {
        "assign",
        {
          {
            "chain",
            name,
            {
              "index",
              len
            }
          }
        },
        {
          value
        }
      }
    }
  end
  local create_accumulate_wrapper
  create_accumulate_wrapper = function(block_pos)
    return function(self, node)
      do
        local _with_0 = self:block("(function()", "end)()")
        local accum_name = _with_0:init_free_var("accum", {
          "table"
        })
        local count_name = _with_0:init_free_var("len", 0)
        local value_name = _with_0:free_name("value", true)
        local inner = node[block_pos]
        inner[#inner] = {
          "assign",
          {
            value_name
          },
          {
            inner[#inner]
          }
        }
        insert(inner, {
          "if",
          {
            "exp",
            value_name,
            "~=",
            "nil"
          },
          table_append(accum_name, count_name, value_name)
        })
        _with_0:stm(node)
        _with_0:stm({
          "return",
          accum_name
        })
        return _with_0
      end
    end
  end
  value_compile = {
    exp = function(self, node)
      local _comp
      _comp = function(i, value)
        if i % 2 == 1 and value == "!=" then
          value = "~="
        end
        return self:value(value)
      end
      do
        local _with_0 = self:line()
        _with_0:append_list((function()
          local _accum_0 = { }
          local _len_0 = 0
          for i, v in ipairs(node) do
            if i > 1 then
              _len_0 = _len_0 + 1
              _accum_0[_len_0] = _comp(i, v)
            end
          end
          return _accum_0
        end)(), " ")
        return _with_0
      end
    end,
    update = function(self, node)
      local _, name = unpack(node)
      self:stm(node)
      return self:name(name)
    end,
    explist = function(self, node)
      do
        local _with_0 = self:line()
        _with_0:append_list((function()
          local _accum_0 = { }
          local _len_0 = 0
          do
            local _item_0 = node
            for _index_0 = 2, #_item_0 do
              local v = _item_0[_index_0]
              _len_0 = _len_0 + 1
              _accum_0[_len_0] = self:value(v)
            end
          end
          return _accum_0
        end)(), ", ")
        return _with_0
      end
    end,
    parens = function(self, node)
      return self:line("(", self:value(node[2]), ")")
    end,
    string = function(self, node)
      local _, delim, inner, delim_end = unpack(node)
      return delim .. inner .. (delim_end or delim)
    end,
    with = function(self, node)
      do
        local _with_0 = self:block("(function()", "end)()")
        _with_0:stm(node, default_return)
        return _with_0
      end
    end,
    ["if"] = function(self, node)
      do
        local _with_0 = self:block("(function()", "end)()")
        _with_0:stm(node, default_return)
        return _with_0
      end
    end,
    comprehension = function(self, node)
      local _, exp, iter = unpack(node)
      do
        local _with_0 = self:block()
        local tmp_name = _with_0:init_free_var("accum", {
          "table"
        })
        local len_name = _with_0:init_free_var("len", 0)
        local action
        action = function(value)
          return table_append(tmp_name, len_name, value)
        end
        _with_0:stm(node, action)
        _with_0:stm({
          "return",
          tmp_name
        })
        if _with_0.has_varargs then
          _with_0.header, _with_0.footer = "(function(...)", "end)(...)"
        else
          _with_0.header, _with_0.footer = "(function()", "end)()"
        end
        return _with_0
      end
    end,
    ["for"] = create_accumulate_wrapper(4),
    foreach = create_accumulate_wrapper(4),
    ["while"] = create_accumulate_wrapper(3),
    chain = function(self, node)
      local callee = node[2]
      if callee == -1 then
        callee = self:get("scope_var")
        if not callee then
          user_error("Short-dot syntax must be called within a with block")
        end
      end
      local sup = self:get("super")
      if callee == "super" and sup then
        return self:value(sup(self, node))
      end
      local chain_item
      chain_item = function(node)
        local t, arg = unpack(node)
        if t == "call" then
          return "(", self:values(arg), ")"
        elseif t == "index" then
          return "[", self:value(arg), "]"
        elseif t == "dot" then
          return ".", arg
        elseif t == "colon" then
          return ":", arg, chain_item(node[3])
        elseif t == "colon_stub" then
          return user_error("Uncalled colon stub")
        else
          return error("Unknown chain action: " .. t)
        end
      end
      local actions
      do
        local _with_0 = self:line()
        do
          local _item_0 = node
          for _index_0 = 3, #_item_0 do
            local action = _item_0[_index_0]
            _with_0:append(chain_item(action))
          end
        end
        actions = _with_0
      end
      if ntype(callee) == "self" and node[3] and ntype(node[3]) == "call" then
        callee[1] = "self_colon"
      end
      local callee_value = self:name(callee)
      if ntype(callee) == "exp" then
        callee_value = self:line("(", callee_value, ")")
      end
      return self:line(callee_value, actions)
    end,
    fndef = function(self, node)
      local _, args, whitelist, arrow, block = unpack(node)
      local default_args = { }
      local format_names
      format_names = function(arg)
        if type(arg) == "string" then
          return arg
        else
          insert(default_args, arg)
          return arg[1]
        end
      end
      args = (function()
        local _accum_0 = { }
        local _len_0 = 0
        do
          local _item_0 = args
          for _index_0 = 1, #_item_0 do
            local arg = _item_0[_index_0]
            _len_0 = _len_0 + 1
            _accum_0[_len_0] = format_names(arg)
          end
        end
        return _accum_0
      end)()
      if arrow == "fat" then
        insert(args, 1, "self")
      end
      do
        local _with_0 = self:block("function(" .. concat(args, ", ") .. ")")
        if #whitelist > 0 then
          _with_0:whitelist_names(whitelist)
        end
        do
          local _item_0 = args
          for _index_0 = 1, #_item_0 do
            local name = _item_0[_index_0]
            _with_0:put_name(name)
          end
        end
        do
          local _item_0 = default_args
          for _index_0 = 1, #_item_0 do
            local default = _item_0[_index_0]
            local name, value = unpack(default)
            _with_0:stm({
              'if',
              {
                'exp',
                name,
                '==',
                'nil'
              },
              {
                {
                  'assign',
                  {
                    name
                  },
                  {
                    value
                  }
                }
              }
            })
          end
        end
        _with_0:ret_stms(block)
        return _with_0
      end
    end,
    table = function(self, node)
      local _, items = unpack(node)
      do
        local _with_0 = self:block("{", "}")
        _with_0.delim = ","
        local format_line
        format_line = function(tuple)
          if #tuple == 2 then
            local key, value = unpack(tuple)
            if type(key) == "string" and data.lua_keywords[key] then
              key = {
                "string",
                '"',
                key
              }
            end
            local assign
            if type(key) ~= "string" then
              assign = self:line("[", _with_0:value(key), "]")
            else
              assign = key
            end
            _with_0:set("current_block", key)
            local out = self:line(assign, " = ", _with_0:value(value))
            _with_0:set("current_block", nil)
            return out
          else
            return self:line(_with_0:value(tuple[1]))
          end
        end
        if items then
          do
            local _item_0 = items
            for _index_0 = 1, #_item_0 do
              local line = _item_0[_index_0]
              _with_0:add(format_line(line))
            end
          end
        end
        return _with_0
      end
    end,
    minus = function(self, node)
      return self:line("-", self:value(node[2]))
    end,
    number = function(self, node)
      return node[2]
    end,
    length = function(self, node)
      return self:line("#", self:value(node[2]))
    end,
    ["not"] = function(self, node)
      return self:line("not ", self:value(node[2]))
    end,
    self = function(self, node)
      return "self." .. self:value(node[2])
    end,
    self_colon = function(self, node)
      return "self:" .. self:value(node[2])
    end,
    raw_value = function(self, value)
      if value == "..." then
        self.has_varargs = true
      end
      return tostring(value)
    end
  }
  
end
package.preload['moonscript.compile.line'] = function()
  module("moonscript.compile", package.seeall)
  local util = require("moonscript.util")
  local data = require("moonscript.data")
  require("moonscript.compile.format")
  require("moonscript.compile.types")
  local reversed = util.reversed
  local ntype = data.ntype
  local concat, insert = table.concat, table.insert
  local constructor_name = "new"
  line_compile = {
    raw = function(self, node)
      local _, text = unpack(node)
      return self:add(text)
    end,
    declare = function(self, node)
      local _, names = unpack(node)
      local undeclared = self:declare(names)
      if #undeclared > 0 then
        do
          local _with_0 = self:line("local ")
          _with_0:append_list((function()
            local _accum_0 = { }
            local _len_0 = 0
            do
              local _item_0 = names
              for _index_0 = 1, #_item_0 do
                local name = _item_0[_index_0]
                _len_0 = _len_0 + 1
                _accum_0[_len_0] = self:name(name)
              end
            end
            return _accum_0
          end)(), ", ")
          return _with_0
        end
      end
    end,
    assign = function(self, node)
      local _, names, values = unpack(node)
      if #values == 1 and cascading[ntype(values[1])] then
        return self:stm({
          "assign",
          names,
          values[1]
        })
      end
      local undeclared = self:declare(names)
      local declare = "local " .. concat(undeclared, ", ")
      if self:is_stm(values) then
        if #undeclared > 0 then
          self:add(declare)
        end
        if cascading[ntype(values)] then
          local decorate
          decorate = function(value)
            return {
              "assign",
              names,
              {
                value
              }
            }
          end
          return self:stm(values, decorate)
        else
          return error("Assigning unsupported statement")
        end
      else
        local has_fndef = false
        local i = 1
        while i <= #values do
          if ntype(values[i]) == "fndef" then
            has_fndef = true
          end
          i = i + 1
        end
        do
          local _with_0 = self:line()
          if #undeclared == #names and not has_fndef then
            _with_0:append(declare)
          else
            if #undeclared > 0 then
              self:add(declare)
            end
            _with_0:append_list((function()
              local _accum_0 = { }
              local _len_0 = 0
              do
                local _item_0 = names
                for _index_0 = 1, #_item_0 do
                  local name = _item_0[_index_0]
                  _len_0 = _len_0 + 1
                  _accum_0[_len_0] = self:value(name)
                end
              end
              return _accum_0
            end)(), ", ")
          end
          _with_0:append(" = ")
          _with_0:append_list((function()
            local _accum_0 = { }
            local _len_0 = 0
            do
              local _item_0 = values
              for _index_0 = 1, #_item_0 do
                local v = _item_0[_index_0]
                _len_0 = _len_0 + 1
                _accum_0[_len_0] = self:value(v)
              end
            end
            return _accum_0
          end)(), ", ")
          return _with_0
        end
      end
    end,
    update = function(self, node)
      local _, name, op, exp = unpack(node)
      local op_final = op:match("^(.+)=$")
      if not op_final then
        error("Unknown op: " .. op)
      end
      return self:stm({
        "assign",
        {
          name
        },
        {
          {
            "exp",
            name,
            op_final,
            exp
          }
        }
      })
    end,
    ["return"] = function(self, node)
      return self:line("return ", self:value(node[2]))
    end,
    ["break"] = function(self, node)
      return "break"
    end,
    import = function(self, node)
      local _, names, source = unpack(node)
      local final_names, to_bind = { }, { }
      do
        local _item_0 = names
        for _index_0 = 1, #_item_0 do
          local name = _item_0[_index_0]
          local final
          if ntype(name) == ":" then
            local tmp = self:name(name[2])
            to_bind[tmp] = true
            final = tmp
          else
            final = self:name(name)
          end
          self:put_name(final)
          insert(final_names, final)
        end
      end
      local get_value
      get_value = function(name)
        if to_bind[name] then
          return moonlib.bind(source, name)
        else
          return source .. "." .. name
        end
      end
      if type(source) == "string" then
        local values = (function()
          local _accum_0 = { }
          local _len_0 = 0
          do
            local _item_0 = final_names
            for _index_0 = 1, #_item_0 do
              local name = _item_0[_index_0]
              _len_0 = _len_0 + 1
              _accum_0[_len_0] = get_value(name)
            end
          end
          return _accum_0
        end)()
        local line
        do
          local _with_0 = self:line("local ", concat(final_names, ", "), " = ")
          _with_0:append_list(values, ", ")
          line = _with_0
        end
        return line
      end
      self:add(self:line("local ", concat(final_names, ", ")))
      do
        local _with_0 = self:block("do")
        source = _with_0:init_free_var("table", source)
        do
          local _item_0 = final_names
          for _index_0 = 1, #_item_0 do
            local name = _item_0[_index_0]
            _with_0:stm({
              "assign",
              {
                name
              },
              {
                get_value(name)
              }
            })
          end
        end
        return _with_0
      end
    end,
    ["if"] = function(self, node, ret)
      local cond, block = node[2], node[3]
      local root
      do
        local _with_0 = self:block(self:line("if ", self:value(cond), " then"))
        _with_0:stms(block, ret)
        root = _with_0
      end
      local current = root
      local add_clause
      add_clause = function(clause)
        local type = clause[1]
        local i = 2
        local next
        if type == "else" then
          next = self:block("else")
        else
          i = i + 1
          next = self:block(self:line("elseif ", self:value(clause[2]), " then"))
        end
        next:stms(clause[i], ret)
        current.next = next
        current = next
      end
      do
        local _item_0 = node
        for _index_0 = 4, #_item_0 do
          local cond = _item_0[_index_0]
          add_clause(cond)
        end
      end
      return root
    end,
    ["while"] = function(self, node)
      local _, cond, block = unpack(node)
      local out
      if is_non_atomic(cond) then
        do
          local _with_0 = self:block("while true do")
          _with_0:stm({
            "if",
            {
              "not",
              cond
            },
            {
              {
                "break"
              }
            }
          })
          out = _with_0
        end
      else
        out = self:block(self:line("while ", self:value(cond), " do"))
      end
      out:stms(block)
      return out
    end,
    ["for"] = function(self, node)
      local _, name, bounds, block = unpack(node)
      local loop = self:line("for ", self:name(name), " = ", self:value({
        "explist",
        unpack(bounds)
      }), " do")
      do
        local _with_0 = self:block(loop)
        _with_0:stms(block)
        return _with_0
      end
    end,
    foreach = function(self, node)
      local _, names, exp, block = unpack(node)
      if ntype(exp) == "unpack" then
        local iter = exp[2]
        local loop
        do
          local _with_0 = self:block()
          local items_tmp = _with_0:free_name("item", true)
          local bounds
          if is_slice(iter) then
            local slice = iter[#iter]
            table.remove(iter)
            table.remove(slice, 1)
            if slice[2] and slice[2] ~= "" then
              local max_tmp = _with_0:init_free_var("max", slice[2])
              slice[2] = {
                "exp",
                max_tmp,
                "<",
                0,
                "and",
                {
                  "length",
                  items_tmp
                },
                "+",
                max_tmp,
                "or",
                max_tmp
              }
            else
              slice[2] = {
                "length",
                items_tmp
              }
            end
            bounds = slice
          else
            bounds = {
              1,
              {
                "length",
                items_tmp
              }
            }
          end
          local index_tmp = _with_0:free_name("index")
          _with_0:stm({
            "assign",
            {
              items_tmp
            },
            {
              iter
            }
          })
          block = (function()
            local _accum_0 = { }
            local _len_0 = 0
            do
              local _item_0 = block
              for _index_0 = 1, #_item_0 do
                local s = _item_0[_index_0]
                _len_0 = _len_0 + 1
                _accum_0[_len_0] = s
              end
            end
            return _accum_0
          end)()
          do
            local _item_0 = names
            for _index_0 = 1, #_item_0 do
              local name = _item_0[_index_0]
              _with_0:shadow_name(name)
            end
          end
          insert(block, 1, {
            "assign",
            names,
            {
              {
                "chain",
                items_tmp,
                {
                  "index",
                  index_tmp
                }
              }
            }
          })
          _with_0:stm({
            "for",
            index_tmp,
            bounds,
            block
          })
          loop = _with_0
        end
        return loop
      end
      local loop
      do
        local _with_0 = self:line()
        _with_0:append("for ")
        _with_0:append_list((function()
          local _accum_0 = { }
          local _len_0 = 0
          do
            local _item_0 = names
            for _index_0 = 1, #_item_0 do
              local name = _item_0[_index_0]
              _len_0 = _len_0 + 1
              _accum_0[_len_0] = self:name(name)
            end
          end
          return _accum_0
        end)(), ", ")
        _with_0:append(" in ", self:value(exp), " do")
        loop = _with_0
      end
      do
        local _with_0 = self:block(loop)
        _with_0:stms(block)
        return _with_0
      end
    end,
    export = function(self, node)
      local _, names = unpack(node)
      self:declare(names)
      return nil
    end,
    class = function(self, node)
      local _, name, parent_val, tbl = unpack(node)
      local constructor = nil
      local final_properties = { }
      do
        local _item_0 = tbl[2]
        for _index_0 = 1, #_item_0 do
          local entry = _item_0[_index_0]
          if entry[1] == constructor_name then
            constructor = entry[2]
          else
            insert(final_properties, entry)
          end
        end
      end
      tbl[2] = final_properties
      local parent_loc = self:free_name("parent", true)
      if not constructor then
        constructor = {
          "fndef",
          {
            "..."
          },
          { },
          "fat",
          {
            {
              "if",
              parent_loc,
              {
                {
                  "chain",
                  "super",
                  {
                    "call",
                    {
                      "..."
                    }
                  }
                }
              }
            }
          }
        }
      end
      smart_node(constructor)
      local self_args = { }
      local get_initializers
      get_initializers = function(arg)
        if ntype(arg) == "self" then
          arg = arg[2]
          insert(self_args, arg)
        end
        return arg
      end
      constructor.args = (function()
        local _accum_0 = { }
        local _len_0 = 0
        do
          local _item_0 = constructor.args
          for _index_0 = 1, #_item_0 do
            local arg = _item_0[_index_0]
            _len_0 = _len_0 + 1
            _accum_0[_len_0] = get_initializers(arg)
          end
        end
        return _accum_0
      end)()
      constructor.arrow = "fat"
      local dests = (function()
        local _accum_0 = { }
        local _len_0 = 0
        do
          local _item_0 = self_args
          for _index_0 = 1, #_item_0 do
            local name = _item_0[_index_0]
            _len_0 = _len_0 + 1
            _accum_0[_len_0] = {
              "self",
              name
            }
          end
        end
        return _accum_0
      end)()
      if #self_args > 0 then
        insert(constructor.body, 1, {
          "assign",
          dests,
          self_args
        })
      end
      local def_scope
      do
        local _with_0 = self:block()
        if parent_val ~= "" then
          parent_val = self:value(parent_val)
        end
        _with_0:put_name(parent_loc)
        _with_0.header = self:line("(function(", parent_loc, ")")
        _with_0.footer = self:line("end)(", parent_val, ")")
        _with_0:set("super", function(block, chain)
          local calling_name = block:get("current_block")
          local slice = (function()
            local _accum_0 = { }
            local _len_0 = 0
            do
              local _item_0 = chain
              for _index_0 = 3, #_item_0 do
                local item = _item_0[_index_0]
                _len_0 = _len_0 + 1
                _accum_0[_len_0] = item
              end
            end
            return _accum_0
          end)()
          slice[1] = {
            "call",
            {
              "self",
              unpack(slice[1][2])
            }
          }
          local act
          if ntype(calling_name) ~= "value" then
            act = "index"
          else
            act = "dot"
          end
          return {
            "chain",
            parent_loc,
            {
              act,
              calling_name
            },
            unpack(slice)
          }
        end)
        local base_name = _with_0:init_free_var("base", tbl)
        _with_0:stm({
          "assign",
          {
            {
              "chain",
              base_name,
              {
                "dot",
                "__index"
              }
            }
          },
          {
            base_name
          }
        })
        _with_0:stm({
          "if",
          parent_loc,
          {
            {
              "chain",
              "setmetatable",
              {
                "call",
                {
                  base_name,
                  {
                    "chain",
                    "getmetatable",
                    {
                      "call",
                      {
                        parent_loc
                      }
                    },
                    {
                      "dot",
                      "__index"
                    }
                  }
                }
              }
            }
          }
        })
        local cls = {
          "table",
          {
            {
              "__init",
              constructor
            }
          }
        }
        local cls_mt = {
          "table",
          {
            {
              "__index",
              base_name
            },
            {
              "__call",
              {
                "fndef",
                {
                  "mt",
                  "..."
                },
                { },
                "slim",
                {
                  {
                    "raw",
                    ("local self = setmetatable({}, %s)"):format(base_name)
                  },
                  {
                    "chain",
                    "mt.__init",
                    {
                      "call",
                      {
                        "self",
                        "..."
                      }
                    }
                  },
                  "self"
                }
              }
            }
          }
        }
        local cls_name = _with_0:init_free_var("class", {
          "chain",
          "setmetatable",
          {
            "call",
            {
              cls,
              cls_mt
            }
          }
        })
        _with_0:stm({
          "assign",
          {
            {
              "chain",
              base_name,
              {
                "dot",
                "__class"
              }
            }
          },
          {
            cls_name
          }
        })
        _with_0:stm({
          "return",
          cls_name
        })
        def_scope = _with_0
      end
      self:stm({
        "declare",
        {
          name
        }
      })
      return self:line(name, " = ", def_scope)
    end,
    comprehension = function(self, node, action)
      local _, exp, clauses = unpack(node)
      if not action then
        action = function(exp)
          return {
            exp
          }
        end
      end
      local current_stms = action(exp)
      for _, clause in reversed(clauses) do
        local t = clause[1]
        if t == "for" then
          local names, iter
          _, names, iter = unpack(clause)
          current_stms = {
            "foreach",
            names,
            iter,
            current_stms
          }
        elseif t == "when" then
          local cond
          _, cond = unpack(clause)
          current_stms = {
            "if",
            cond,
            current_stms
          }
        else
          current_stms = error("Unknown comprehension clause: " .. t)
        end
        current_stms = {
          current_stms
        }
      end
      return self:stms(current_stms)
    end,
    with = function(self, node, ret)
      local _, exp, block = unpack(node)
      do
        local _with_0 = self:block()
        local var = _with_0:init_free_var("with", exp)
        self:set("scope_var", var)
        _with_0:stms(block)
        if ret then
          _with_0:stm(ret(var))
        end
        return _with_0
      end
    end
  }
  
end
package.preload['moonscript.compile.types'] = function()
  module("moonscript.compile", package.seeall)
  local util = require("moonscript.util")
  local data = require("moonscript.data")
  local ntype = data.ntype
  local key_table = {
    fndef = {
      "args",
      "whitelist",
      "arrow",
      "body"
    }
  }
  local build_table
  build_table = function()
    for key, value in pairs(key_table) do
      local index = { }
      for i, name in ipairs(value) do
        index[name] = i + 1
      end
      key_table[key] = index
    end
  end
  build_table()
  smart_node = function(node)
    local index = key_table[ntype(node)]
    if not index then
      return node
    end
    return setmetatable(node, {
      __index = function(node, key)
        if index[key] then
          return rawget(node, index[key])
        elseif type(key) == "string" then
          return error("unknown key: `" .. key .. "` on node type: `" .. ntype(node) .. "`")
        end
      end,
      __newindex = function(node, key, value)
        if index[key] then
          key = index[key]
        end
        return rawset(node, key, value)
      end
    })
  end
  
end
package.preload['moonscript.compile.format'] = function()
  module("moonscript.compile", package.seeall)
  local util = require("moonscript.util")
  local data = require("moonscript.data")
  local Set, ntype = data.Set, data.ntype
  local concat, insert = table.concat, table.insert
  indent_char = "  "
  user_error = function(...)
    return error({
      "user-error",
      ...
    })
  end
  local manual_return = Set({
    "foreach",
    "for",
    "while"
  })
  default_return = function(exp)
    local t = ntype(exp)
    if t == "chain" and exp[2] == "return" then
      local items = {
        "explist"
      }
      do
        local _item_0 = exp[3][2]
        for _index_0 = 1, #_item_0 do
          local v = _item_0[_index_0]
          insert(items, v)
        end
      end
      return {
        "return",
        items
      }
    elseif manual_return[t] then
      return exp
    else
      return {
        "return",
        exp
      }
    end
  end
  moonlib = {
    bind = function(tbl, name)
      return concat({
        "moon.bind(",
        tbl,
        ".",
        name,
        ", ",
        tbl,
        ")"
      })
    end
  }
  cascading = Set({
    "if",
    "with"
  })
  non_atomic = Set({
    "update"
  })
  has_value = function(node)
    if ntype(node) == "chain" then
      local ctype = ntype(node[#node])
      return ctype ~= "call" and ctype ~= "colon"
    else
      return true
    end
  end
  is_non_atomic = function(node)
    return non_atomic[ntype(node)]
  end
  is_slice = function(node)
    return ntype(node) == "chain" and ntype(node[#node]) == "slice"
  end
  count_lines = function(str)
    local count = 1
    for _ in str:gmatch("\n") do
      count = count + 1
    end
    return count
  end
  
end
package.preload['moonscript.dump'] = function()
  module("moonscript.dump", package.seeall)
  local flat_value
  flat_value = function(op, depth)
    if depth == nil then
      depth = 1
    end
    if type(op) == "string" then
      return '"' .. op .. '"'
    end
    if type(op) ~= "table" then
      return tostring(op)
    end
    local items = (function()
      local _accum_0 = { }
      local _len_0 = 0
      do
        local _item_0 = op
        for _index_0 = 1, #_item_0 do
          local item = _item_0[_index_0]
          _len_0 = _len_0 + 1
          _accum_0[_len_0] = flat_value(item, depth + 1)
        end
      end
      return _accum_0
    end)()
    local pos = op[-1]
    return "{" .. (pos and "[" .. pos .. "] " or "") .. table.concat(items, ", ") .. "}"
  end
  value = function(op)
    return flat_value(op)
  end
  tree = function(block)
    return (function()
      local _accum_0 = { }
      local _len_0 = 0
      do
        local _item_0 = block
        for _index_0 = 1, #_item_0 do
          local value = _item_0[_index_0]
          _len_0 = _len_0 + 1
          _accum_0[_len_0] = print(flat_value(value))
        end
      end
      return _accum_0
    end)()
  end
  
end
package.preload['moonscript.errors'] = function()
  module("moonscript.errors", package.seeall)
  local moon = require("moonscript")
  local util = require("moonscript.util")
  require("lpeg")
  local concat, insert = table.concat, table.insert
  local split, pos_to_line = util.split, util.pos_to_line
  local lookup_line
  lookup_line = function(fname, pos, cache)
    if not cache[fname] then
      do
        local _with_0 = io.open(fname)
        cache[fname] = _with_0:read("*a")
        _with_0:close()
      end
    end
    return pos_to_line(cache[fname], pos)
  end
  local reverse_line_number
  reverse_line_number = function(fname, line_table, line_num, cache)
    for i = line_num, 0, -1 do
      if line_table[i] then
        return lookup_line(fname, line_table[i], cache)
      end
    end
    return "unknown"
  end
  rewrite_traceback = function(text, err)
    local line_tables = moon.line_tables
    local V, S, Ct, C = lpeg.V, lpeg.S, lpeg.Ct, lpeg.C
    local header_text = "stack traceback:"
    local Header, Line = V("Header"), V("Line")
    local Break = lpeg.S("\n")
    local g = lpeg.P({
      Header,
      Header = header_text * Break * Ct(Line ^ 1),
      Line = "\t" * C((1 - Break) ^ 0) * (Break + -1)
    })
    local cache = { }
    local rewrite_single
    rewrite_single = function(trace)
      local fname, line, msg = trace:match('^%[string "(.-)"]:(%d+): (.*)$')
      local tbl = line_tables[fname]
      if fname and tbl then
        return concat({
          fname,
          ":",
          reverse_line_number(fname, tbl, line, cache),
          ": ",
          msg
        })
      else
        return trace
      end
    end
    err = rewrite_single(err)
    local match = g:match(text)
    for i, trace in ipairs(match) do
      match[i] = rewrite_single(trace)
    end
    return concat({
      "moon:" .. err,
      header_text,
      "\t" .. concat(match, "\n\t")
    }, "\n")
  end
  
end
return package.preload["moonscript"]()
