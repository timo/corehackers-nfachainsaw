[![Actions Status](https://github.com/timo/corehackers-nfachainsaw/actions/workflows/linux.yml/badge.svg)](https://github.com/timo/corehackers-nfachainsaw/actions) [![Actions Status](https://github.com/timo/corehackers-nfachainsaw/actions/workflows/macos.yml/badge.svg)](https://github.com/timo/corehackers-nfachainsaw/actions) [![Actions Status](https://github.com/timo/corehackers-nfachainsaw/actions/workflows/windows.yml/badge.svg)](https://github.com/timo/corehackers-nfachainsaw/actions)

NAME
====

CoreHackers::NfaChainsaw - Utility program to introspect NFAs used by NQP and for experimentation.

SYNOPSIS
========

```bash
# Launch nfa_chainsaw, filter Perl6::Grammar methods/regexes by "termish"
$ nfa_chainsaw termish

# [... lots of output ...]

    0      10 states: capterm
    1       5 states: capterm[0]
    2      46 states: defterm
    3       4 states: eat_terminator[0]
    4      30 states: eat_terminator[1]
    5   21885 states: term protoregex
    6   21885 states: term protoregex
    7       5 states: term:sym<...>
    8       3 states: term:sym<...>[1]
    9       8 states: term:sym<identifier>
   10      15 states: term:sym<multi_declarator>[0]
   11       3 states: term:sym<rand>[0]
   12       3 states: term:sym<reduce>[1]
   13      68 states: terminator protoregex
   14    8809 states: termish

s, j: Save NFAs to files (States list or Json)
q: Abort
Choice: 

# choose j for json saving

Make your choice...
  [ ]     0      10 states: capterm
  [ ]     1       5 states: capterm[0]
  [ ]     2      46 states: defterm
  [X]     3       4 states: eat_terminator[0]
  [X]     4      30 states: eat_terminator[1]
  [ ]     5   21885 states: term protoregex
  [ ]     6   21885 states: term protoregex
  [ ]     7       5 states: term:sym<...>
  [ ]     8       3 states: term:sym<...>[1]
  [ ]     9       8 states: term:sym<identifier>
  [ ]    10      15 states: term:sym<multi_declarator>[0]
  [ ]    11       3 states: term:sym<rand>[0]
  [ ]    12       3 states: term:sym<reduce>[1]
  [ ]    13      68 states: terminator protoregex
  [ ]    14    8809 states: termish

number: toggle an entry
number other third: toggle some entries
number..* / *..number: toggle from entry to end or beginning to entry
number..other: toggle range of entries
  (use ^ before and/or after .. to exclude ends)
*: toggle all
r: reset all to Off
enter: done, accept changes
q: abort

Choice: 
saved     3       4 states: eat_terminator[0] to /.../nfa_chainsaw/nfa_VANQEUJB-eat_terminator[0]-statelist.json: 131 bytes
saved     4      30 states: eat_terminator[1] to /.../nfa_chainsaw/nfa_VANQEUJB-eat_terminator[1]-statelist.json: 651 bytes

# choose 10 for term:sym<multi_declarator>[0]

current state: {active => [State(1 from [])], nfa-basename => term:sym<multi_declarator>, nfa-name => term:sym<multi_declarator>[0], offset => 0, parent-state => (Any), states => {fates => 3, states => 15}, text => }

Current text:
  ""


Possible theoretical inputs:

0: 
    "l"

1: 13
    "o"

2: 3
    "m"

3: 8
    "p"

c: Enter your own
b: go back one
s: go back to the start
a: automatically explore
e: show edges of currently active states
o: re-do optimization with variants turned on or off
q: stop
Make your choice: 

# show edges of currently active states

==========================================
   16 states
Fates:
        [0 1 2]

1:
        3 CODEPOINT m
        8 CODEPOINT p
        13 CODEPOINT o
```

DESCRIPTION
===========

CoreHackers::NfaChainsaw provides a menu-driven CLI for extracting, introspecting, running, and exploring NFAs present in rakudo.

It began its life as a port of the NFA optimizer from NQP's `QRegex/NFA.nqp`, then gained the ability to simulate matching an NFA against a string, followed by more random stuff being bolted on to the side.

With the optimizer ported to Raku, and a matcher as an alternative implementation of `nqp_nfa_run` from MoarVM, I hope that this code is a good read (and toy) if you want to figure out how NFAs are created, how they look on the inside, how they are optimized, and how they are run.

The structure of the module allows more optimization passes to be added in the code, and for different variations of optimization passes to be compared.

