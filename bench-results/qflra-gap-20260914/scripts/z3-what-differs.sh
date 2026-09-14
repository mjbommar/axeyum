#!/usr/bin/env bash
# What does the solver that succeeds DO differently?
#
# Our census says 74 of 93 undecided rows die in one OFFLINE DENSE engine.  The
# claim to test is that z3 never builds a dense tableau of that shape.  z3's own
# `-st` statistics name the engine and its size, so this is z3 reporting on
# itself rather than us inferring from a verdict.
F="$1"
echo "### $F"
echo "-- asserts / declares --"
grep -c '(assert' "$F"
grep -c 'declare-fun' "$F"
echo "-- z3 -st, 24 s --"
timeout 40 z3 -T:24 -st "$F" 2>&1 | grep -E '^(sat|unsat|unknown)$|arith|simplex|memory|rlimit|conflicts|decisions' | head -25
