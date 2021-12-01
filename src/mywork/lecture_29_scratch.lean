import tactic.ring

begin
  exact nat.succ (nat.succ t)
end

def inc' : nat → nat := --increment
begin
  assume n,
  exact nat.succ n
end

def inc : nat → nat
| n := nat.succ n

def dec : nat → nat  --decrement
| (nat.zero) := nat.zero
| (nat.succ n') := n' 

def add : nat → nat → nat 
| (nat.zero) (m) := m
| (nat.succ n') (m) := nat.succ (add n' m)

def mul : nat → nat → nat --multiply (iterated addition)
| (nat.zero) (m) := nat.zero 
| (nat.succ n') (m) := add (m) (mul n' m)

def exp : nat → nat → nat --exponent (iterated multiplication)
| (nat.zero) (m) := 1
| (nat.succ n') (m) := mul (m) (exp n' m)

def sum_to : nat → nat 
| (nat.zero) := nat.zero
| (nat.succ n') := add (sum_to n') (inc n')