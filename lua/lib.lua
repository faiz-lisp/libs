
-- my lua - lib.lua v0.01 - Faiz --

--[[ 
  require "lib"
  -- _G 是一个特殊的table，用于保存所有的全局变量 
--]]

--[[
- others
  - nil
  - echo
  - x.pre-lua -> x.lua: func, ret
- lisp
  - cons
  - car
  - cdr
  - quote  
  - eq: ==
  - atom
  - cond
  - lam:
  - ev
  - list: vector/array?
  - apply
  - map
  - cps
  - syms
  - cost
--]]

function cons (a, d)
  return {CAR=a, CDR=d}
end

function car (xs)
  return xs.CAR
end

function cdr (xs)
  return xs.CDR
end

---

-- function list (x, ...)
  -- {...}
  -- return cons(x, )
-- end
-- lis = list

echo = print

evs = loadstring

---

g_num = 42
-- echo (g_num)
g_num= nil -- gc

---

xs = cons (2, cons (1, nil))
x = car (cdr (xs))
echo (x)
