#!/usr/bin/env rakudo
use nqp;
use Perl6::Grammar:from<NQP>;
use QRegex:from<NQP>;

use JSON::Fast;

sub recursive-hllize(Mu $in) {
  my $h = nqp::hllize($in);
  if $h ~~ Positional {
    my @result = do recursive-hllize($_).item for @$h;
    return @result;
  }
  elsif $h ~~ Hash {
      die "ack";
  }
  elsif !$h.DEFINITE {
      return Any;
  }
  else {
      return $h;
  }
}

multi sub stateslist-to-json(@states) {
    my @hllized = recursive-hllize(@states);
    "["
    ~ to-json(@hllized[0]) ~ ",\n"
    ~ (
        do for @hllized.skip(1) -> @edges {
        "  ["
        ~ (do for @edges.rotor(3, :partial) -> $triple {
          $triple.map({ to-json($_, :!pretty) }).join(", ")
        }).join(",\n   ") ~ "]"
    }).join(",\n")
    ~ "\n]\n";
}

my $*DEBUG_VERBOSE = 0;

my $match = Perl6::Grammar.new;

my Mu $protoregex_meth := $match.^find_method("!protoregex_table");

my Mu $qregex_nfa_class := QRegex::NFA;

my $modified_nfa = $qregex_nfa_class but role { method optimize { return my-optimize(self); } }

sub prompt(\c) {
    my $res := &CORE::prompt(|c);
    if $*IN.eof {
        die "User closed the input stream";
    }
    $res;
}

say "protoregex table:";
say nqp::hllize($protoregex_meth($match)).keys;
say "";

my $ACTIONS := [
  'FATE',
  'EPSILON',
  'CODEPOINT',
  'CODEPOINT_NEG',
  'CHARCLASS',
  'CHARCLASS_NEG',
  'CHARLIST',
  'CHARLIST_NEG',
  'SUBRULE',
  'CODEPOINT_I',
  'CODEPOINT_I_NEG',
  'GENERIC_VAR',
  'CHARRANGE',
  'CHARRANGE_NEG',
  'CODEPOINT_LL',
  'CODEPOINT_I_LL',
  'CODEPOINT_M',
  'CODEPOINT_M_NEG',
  'CODEPOINT_M_LL',
  'CODEPOINT_IM',
  'CODEPOINT_IM_NEG',
  'CODEPOINT_IM_LL',
  'CHARRANGE_M',
  'CHARRANGE_M_NEG'
];

my %cclass_names = (
    nqp::const::CCLASS_ANY => "ANY",
    nqp::const::CCLASS_UPPERCASE => "UPPERCASE",
    nqp::const::CCLASS_LOWERCASE => "LOWERCASE",
    nqp::const::CCLASS_ALPHABETIC => "ALPHABETIC",
    nqp::const::CCLASS_NUMERIC => "NUMERIC",
    nqp::const::CCLASS_HEXADECIMAL => "HEXADECIMAL",
    nqp::const::CCLASS_WHITESPACE => "WHITESPACE",
    nqp::const::CCLASS_PRINTING => "PRINTING",
    nqp::const::CCLASS_BLANK => "BLANK",
    nqp::const::CCLASS_CONTROL => "CONTROL",
    nqp::const::CCLASS_PUNCTUATION => "PUNCTUATION",
    nqp::const::CCLASS_ALPHANUMERIC => "ALPHANUMERIC",
    nqp::const::CCLASS_NEWLINE => "NEWLINE",
    nqp::const::CCLASS_WORD => "WORD",
);

sub dump_state($s, @edges) {
    say("$s:");
    for @edges.list -> $a, $v, $t {
        my $act = nqp::bitand_i($a,0xff);
        my $action = $ACTIONS[$act];
        if $act == nqp::const::EDGE_CODEPOINT
            || $act == nqp::const::EDGE_CODEPOINT_LL {
            say("\t$t $action " ~ nqp::chr($v));
        }
        elsif $act == nqp::const::EDGE_FATE {
            say("\t$t $action " ~ $v.raku);
        }
        elsif $act == nqp::const::EDGE_CHARCLASS
            || $act == nqp::const::EDGE_CHARCLASS_NEG {
            say("\t$t $action " ~ $v.raku);
        }
        elsif $act == nqp::const::EDGE_CHARLIST
            || $act == nqp::const::EDGE_CHARLIST_NEG {
            say("\t$t $action " ~ $v);
        }
        elsif $act == nqp::const::EDGE_SUBRULE
            && nqp::istype($v,str) {
            say("\t$t $action " ~ $v);
        }
        elsif $act == nqp::const::EDGE_CHARRANGE | nqp::const::EDGE_CHARRANGE_M | nqp::const::EDGE_CHARRANGE_NEG | nqp::const::EDGE_CHARRANGE_M_NEG {
            say("\t$t $action ", $v);
        }
        else {
            say("\t$t $action");
        }
    }
    say("");
}

sub mydump(@states, :@only_states) {
    my int $send = +@states;
    if $send > 1 {
        say("==========================================\n   $send states");
        say("Fates:");
        for @states[0] -> $f {
            $f = "" if nqp::isnull($f);
            say("\t$f.gist()");
        }
        say("");
        for (@only_states || 1..^@states) -> $s {
            dump_state($s, @states[$s]);
        }
    }
}

sub ORIG_find_single_epsilon_states(@states) {
  my @remap;
  for 1..^@states -> $stateidx {
    my @state := @states[$stateidx];
    next unless @state.elems == 3;
    my $to = @state[2];
    my $act = @state[0];
    if $act == nqp::const::EDGE_EPSILON {
      @remap[$stateidx] = $to;
      #say "  remap for $stateidx is now $to";
    }
    elsif $act == nqp::const::EDGE_FATE && $to {
      while @remap[$to] {
        #say "  chasing fate 'to' from $to to @remap[$to]";
        $to = @remap[$to];
      }

      my @tostate := @states[$to];
      if @tostate >= 0 && @tostate[0] == nqp::const::EDGE_FATE && @tostate[1] == @state[1] {
        #say "  -> remap for $stateidx is now $to";
        @remap[$stateidx] = $to;
      }
    }
  }

  if $*DEBUG_VERBOSE > 1 {
    for 1..^@states {
      if @remap[$_] {
        say("\t$_ -> @remap[$_]");
      }
    }
  }

  say("\n\nnow @states.elems() states before unlinking empties\n") if $*DEBUG_VERBOSE > 0;

  say (now - ENTER now), "  remapping has @remap.grep(none(0)).elems() elements" if $*DEBUG_VERBOSE > 0;

  return @remap;
}

sub ORIG_clear_remapped_and_count_incoming(@states, @remap) {
  my @incoming;
  my $cleared = 0;
  my $chased = 0;
  for 1..^@states {
    if @remap[$_] {
      #say "clearing state $_, used to be ", @states[$_];
      @states[$_] = [];
      $cleared++;
      next;
    }

    #say "updating state $_, used to be ", @states[$_];

    my @state := @states[$_];
    #if @state > 3 {
    #  note "state $_/@states.elems() has @state.elems() elements";
    #}
    my int $e = 2;
    my int $eend = +@state;
    while $e < $eend {
      my $to = @state[$e];
      my $was = $to;
      if $to {
        my $newto = $to;
        while @remap[$newto] -> $mapped {
          $chased++;
          $newto = $mapped;
          say "  chasing $was to $newto" if $*DEBUG_VERBOSE > 0;
        }

        if $newto != $to {
          @state[$e] = $newto;
        }

        @incoming[$newto]++;
      }
      $e += 3;
    }
  }

  say("\n\nnow @states.elems() states before stealing singleton edges\n") if $*DEBUG_VERBOSE > 0;

  say (now - ENTER now), "  cleared $cleared states, followed the mapping $chased steps" if $*DEBUG_VERBOSE > 0;
  return @incoming;
}


sub CUSTOM_steal_edges_from_all_states_epsilon_reachable_from_start(@states, @incoming) {
  my $removed = 0;
  my int @work = 1;
  my int @seen;

  my @newedges;
  my @oldedges = @states[1].list;

  say "start state edges: ", @oldedges.raku if $*DEBUG_VERBOSE > 0;

  while @work {
    my $item = @work.pop;

    next if @seen[$item]++;

    say "    considering state $item for edge stealing;" if $*DEBUG_VERBOSE > 0;

    my @state := @states[$item];
    say "      states: @state[]" if $*DEBUG_VERBOSE > 0;

    # don't reduce incoming count for start state, that would be silly.
    #my $was_removed = False;
    #if $item != 1 {
    #  if --@incoming[$item] == 0 {
    #    $removed++;
    #    $was_removed = True;
    #  }
    #}

    my int $e = 2;
    my int $eend = +@state;
    while $e < $eend {
      my $act = @state[$e - 2] +& 0xff;
      my $to = @state[$e];

      if $act == nqp::const::EDGE_EPSILON {
        say "      epsilon!" if $*DEBUG_VERBOSE > 0;
        @work.push($to);
      }
      else {
        my $v = @state[$e - 1];
        say "      $ACTIONS[$act]!" if $*DEBUG_VERBOSE > 0;
        @newedges.push([@state[$e - 2], $v, $to]);
      }

      $e += 3;
    }

    #if $was_removed {
    #  say "clearing out state $item";
    #  @states[$item] := [];
    #}
  }

  @newedges .= sort(*.[1]);
  @newedges = @newedges.map(*.Slip).list;

  @states[1] = @newedges;
  
  say (now - ENTER now), "  removed $removed states after stealing edges from stuff reachable with epsilon from start state." if $*DEBUG_VERBOSE > 0;
  if $*DEBUG_VERBOSE > 0 {
    say "    @seen.grep(* != 0).elems() states in the epsilon-closure of state 1:  @seen.pairs().grep(*.value != 0).map(*.key)";
    say "    state 1 used to have @oldedges.elems() elements, now has @newedges.elems()";
  }
}

sub ORIG_steal_from_single_edge_states_behind_epsilon(@states, @incoming) {
  my $removed = 0;
  for 1..^@states -> $stateidx {
    my @state := @states[$stateidx];
    my int $eend = +@state;
    my int $e = 2;
    while $e < $eend {
      my $to = @state[$e];
      my $act = @state[$e - 2];
      if $act == nqp::const::EDGE_EPSILON && $to {
        my $tostate := @states[$to];
        if $tostate.elems == 3 {

          if $*DEBUG_VERBOSE > 1 {
            say "  $stateidx stealing $to";
          }

          @state[$e - 2] = $tostate[0];
          @state[$e - 1] = $tostate[1];
          @state[$e    ] = $tostate[2];
  
          if --@incoming[$to] == 0 {
            say "    clearing out unused state $to" if $*DEBUG_VERBOSE > 0;
            @states[$to] = [];
            $removed++;
          }
        }
      }
      $e += 3;
    }
  }

  say("\n\nnow @states.elems() states before calculating remap\n") if $*DEBUG_VERBOSE > 0;

  say (now - ENTER now), "  removed $removed states that were no longer referenced." if $*DEBUG_VERBOSE > 0;
}

sub ORIG_resequence_states_to_skip_empty(@states) {
  my @remap;
  my $newend = 0;
  for 1..^@states {
    @remap[$_] = (@states[$_].elems == 0 ?? 0 !! ++$newend);
  }

  say("\n\nnow @states.elems() states\n") if $*DEBUG_VERBOSE > 0;

  if $*DEBUG_VERBOSE > 1 {
    if $*DEBUG_VERBOSE > 2 {
      mydump(@states);
    }
    for 1..^@states {
        if @remap[$_] {
        say("\t$_ -> @remap[$_]");
        }
    }
  }

  say("\n\nnow @states.elems() states mapping to $newend states\n") if $*DEBUG_VERBOSE > 0;

  say (now - ENTER now), "  remapping has @remap.grep(none(0)).elems() elements" if $*DEBUG_VERBOSE > 0;
  say "  new length of state array is $newend, was @states.elems()" if $*DEBUG_VERBOSE > 0;

  return @remap;
}

sub ORIG_move_states_for_resequence(@states, @remap) {
  my @newstates;
  @newstates[0] = @states[0];

  my $dups_deleted = 0;

  for 1..^@states {
    my $s = $_;
    my @state := @states[$_];
    say "Skipping $_" if @state == 0 and $*DEBUG_VERBOSE > 0;
    next if @state == 0;
    my $newpos = @remap[$_];

    if $newpos {
      say "state $newpos is a clone of state $_" if $*DEBUG_VERBOSE > 0;

      my int $eend = +@state;
      my int $e = 2;
      while $e < $eend {
        my $to = @state[$e];
        my $act = @state[$e - 2] +& 0xff;

        if $to {
            @state[$e] = @remap[$to];
            if $*DEBUG_VERBOSE > 1 {
              say "In $s -> $newpos remapping $ACTIONS[$act] $to -> @remap[$to]";
            }
        }
        $e += 3;
      }

      # the "small O(N^2) dup remover" from NFA.nqp
      $e = 3;
      while $e < $eend {
        my $act = @state[$e] +& 0xff;
        if $act < nqp::const::EDGE_CHARLIST {
          my int $f;
          while $f < $e {
            if $act == @state[$f]
                && @state[$e + 2] == @state[$f + 2]
                && @state[$e + 1] == @state[$f + 1] {
              # delete the duplicate edge
              say("Deleting dup edge at $s $e/$f") if $*DEBUG_VERBOSE > 0;
              @state.splice($e, 3, []);
              $dups_deleted++;
              $f = $e;
              $e -= 3;
              $eend -= 3;
            }
            $f += 3;
          }
        }
        $e += 3;
      }

      @newstates[$newpos] = @state;
    }
    else {
      say("Skipping $_");
    }
  }



  say (now - ENTER now), "  deleted $dups_deleted duplicate edges" if $*DEBUG_VERBOSE > 0;
  @newstates;
}

class HLLNFA {
  has @.states is rw;
  method save { @.states }
}

my @known_variants = <original steal_from_start_early steal_from_start_late>;
my @*OPT_VARIANTS = <original>;
my $*OPT_VARIANT;
my &*GET_OPT_OUTPUT = -> Mu $nfa, $variant { $*OUT };

sub my-optimize(Mu $nfa) {
  my $variant = $*OPT_VARIANT;

  my $*OUT = &*GET_OPT_OUTPUT($nfa, $variant);

  my @states = recursive-hllize($nfa.states);

  if @states <= 2 { return HLLNFA.new(:@states) }

  if $*DEBUG_VERBOSE > 0 {
    say "BEGIN OF OPTIMIZATION - variant: $variant";
  }

  if $*DEBUG_VERBOSE > 2 {
    #dd :@states;
    mydump(@states);
  }

  my @remap = ORIG_find_single_epsilon_states(@states);

  if $*DEBUG_VERBOSE > 2 {
    #dd :@states;
    mydump(@states);
  }

  #dd :@remap;

  my @incoming = ORIG_clear_remapped_and_count_incoming(@states, @remap);

  #dd :@states, :@incoming;
  #dd :@states;

  if $*DEBUG_VERBOSE > 2 {
    mydump(@states);
  }

  ORIG_steal_from_single_edge_states_behind_epsilon(@states, @incoming);

  if $variant.contains("steal_from_start_early") {
    say "running steal_from_start_early variant";
    CUSTOM_steal_edges_from_all_states_epsilon_reachable_from_start(@states, @incoming);
  }

  #dd :@states;

  # dd :@states;

  my @resequence = ORIG_resequence_states_to_skip_empty(@states);
  # dd :@resequence;

  #mydump(@states);

  @states = ORIG_move_states_for_resequence(@states, @resequence);

  if $variant.contains("steal_from_start_late") {
    say "running steal_from_start_late variant";
    CUSTOM_steal_edges_from_all_states_epsilon_reachable_from_start(@states, @incoming);
  }

  if $*DEBUG_VERBOSE > 2 {
    #dd :@states;
    mydump(@states);
  }

  if $*DEBUG_VERBOSE > 0 {
    say "END OF OPTIMIZATION";
  }

  return HLLNFA.new(:@states);
}

sub my_alt_nfa(Mu $self, Mu $regex, str $name, Mu $nfa_class = $modified_nfa) {
    my Mu $nfa     := $nfa_class.new;
    my Mu $altnfas := $regex.ALT_NFA($name);

    # say "my_ant_nfa for regex $regex.name() name $name, there are $altnfas.elems() alt nfas";
    # .say for @$altnfas;

    my int $start = 1;
    my int $m     = +$altnfas;
    my int $fate;
    while $fate < $m {
        # say "will merge substates $start, 0, $fate, altnfas[$fate], self";
        my $mss_meth := $nfa.^find_method("mergesubstates");
        $mss_meth($nfa,
          $start, 0, $fate, nqp::atpos(nqp::getattr($altnfas, List, '$!reified'), $fate), $self
        );
        ++$fate;
    }

    $nfa.optimize
}

sub my_protoregex_nfa(Mu $self, $name, Mu $nfa_class = $modified_nfa) {
    my $protorx := $self.HOW.cache(
      $self, "!protoregex_table", { $self."!protoregex_table"() }
    );
    my Mu $nfa   := $nfa_class.new;
    
    my $states_meth := $nfa.^find_method("states");
    my Mu $fates := nqp::atpos($states_meth($nfa), 0);

    #say "my protoregex nfa for $name";

    my int $start = 1;
    my int $fate;
    my Mu $rxes := nqp::atkey($protorx, $name);
    unless nqp::isnull($rxes) {
        my int $m = nqp::elems($rxes);
        my int $i;
        while $i < $m {
            my $rxname := nqp::atpos($rxes, $i);
            ++$fate;
            my $msr_meth := $nfa.^find_method("mergesubrule");
            #say "merge substates for nfa, $start, 0, $fate, self, $rxname";
            $msr_meth($nfa,
              $start, 0, $fate, $self<>, $rxname
            );
            nqp::bindpos($fates, $fate, $rxname);  # override default fate #
            ++$i;
        }
    }

    $nfa.optimize
}

class NFAFromGrammar is rw {
    has $.states;
    has $.nfa-name;
    has $.basename;
}

my NFAFromGrammar @all-nfas;

sub output-nfas-for-code($name, Mu $m, $indent = "   ", :$basename_for_regen = $name, :$full_filter = Str) {
  say $indent ~ " name: " ~ $_ with $name;

  say "$indent   raw NFA: ", nqp::hllize($_).raku with $m.?NFA;

  if $m.?ALT_NFAS {
    my %alt_nfas := nqp::hllize($m.ALT_NFAS);
    for %alt_nfas {
      say "$indent   $_.key(): " ~ recursive-hllize($_.value()).raku;

      for @*OPT_VARIANTS -> $*OPT_VARIANT {
        my $thename = @*OPT_VARIANTS > 1 ?? $name ~ "-opt-$*OPT_VARIANT" !! $name;

        with $full_filter {
          next if $name ne $full_filter && $thename ne $full_filter;
        }

        my $alt_nfa := my_alt_nfa($match, $m, $_.key);
        my @states := recursive-hllize($alt_nfa.states);
        @all-nfas.push(NFAFromGrammar.new(nfa-name => $thename, states => @states, basename => $basename_for_regen));
        say $indent ~ "     instantiated $thename: " ~ @states.raku;
      }

      #if @states > 2 {
        #{
        #  my $*OUT = "/tmp/optimizer.$($_.key).ported.txt".IO.open(:w);
        #  mydump(@states);
        #  $*OUT.close;
        #}
        #
        #{
        #  my $*OUT = "/tmp/optimizer.$($_.key).orig.txt".IO.open(:w);
        #  my $protoregex_nfa := my_alt_nfa($match, $m, $_.key, QRegex::NFA);
        #  if $protoregex_nfa.save != 0 {
        #    mydump($protoregex_nfa.save);
        #  }
        #  $*OUT.close;
        #}
      #}
    }
  }
  
  if $m.?NESTED_CODES.DEFINITE {
    for 0..* Z nqp::hllize($m.NESTED_CODES) -> ($idx, $c) {
      output-nfas-for-code($name ~ "[" ~ $idx ~ "]", $c, $indent ~ "  ", :$basename_for_regen, :$full_filter);
    }
  }

  for @*OPT_VARIANTS -> $*OPT_VARIANT {
    my $thename = @*OPT_VARIANTS > 1 ?? $name ~ "-opt-$*OPT_VARIANT" !! $name;

    with $full_filter {
      return if $thename ne $full_filter && $name ne $full_filter && $name ~ " protoregex" ne $full_filter;
    }

    my $protoregex_nfa := my_protoregex_nfa($match, $m.name);
    my @states = recursive-hllize($protoregex_nfa.states);

    if @states > 2 && @states[0] != 0 && @states[1] != 0 {
      @all-nfas.push(NFAFromGrammar.new(nfa-name => ($thename ~ " protoregex"), states => @states, basename => $basename_for_regen));
      say $indent ~ " instantiated protoregex_nfa: " ~ @states.raku;
    }
  }
}

sub is-edge-negated($masked-act) {
    return so $masked-act == any(
        nqp::const::EDGE_CODEPOINT_NEG,
        nqp::const::EDGE_CHARCLASS_NEG,
        nqp::const::EDGE_CHARLIST_NEG,
        nqp::const::EDGE_CODEPOINT_I_NEG,
        nqp::const::EDGE_CHARRANGE_NEG,
        nqp::const::EDGE_CODEPOINT_M_NEG,
        nqp::const::EDGE_CODEPOINT_IM_NEG,
        nqp::const::EDGE_CHARRANGE_M_NEG);
}

sub does-edge-match($edge, $character) {
    my $masked_act = $edge[0] +& 0xff;
    my $negated = is-edge-negated($masked_act);
    my $actname = $ACTIONS[$masked_act];
    my $v = $edge[1];
    # say "  does $edge.raku() ($masked_act == $actname) match $character.raku()? (negated? $negated)";
    my $result = do given $masked_act {
        when nqp::const::EDGE_FATE {
            # say "    fate edge";
            True
        }
        when nqp::const::EDGE_EPSILON {
            # say "    epsilon edge";
            True
        }
        when nqp::const::EDGE_CODEPOINT | nqp::const::EDGE_CODEPOINT_NEG | nqp::const::EDGE_CODEPOINT_LL {
            $character eq ($v ~~ Int ?? chr($v) !! $v);
        }
        when nqp::const::EDGE_CHARCLASS | nqp::const::EDGE_CHARCLASS_NEG {
            # say "    cclass edge";
            nqp::iscclass($v, $character, 0)
        }
        when nqp::const::EDGE_CHARLIST | nqp::const::EDGE_CHARLIST_NEG {
            # say "    does $v.raku() contain $character.raku()? ", $v.contains($character);
            $v.contains($character);
        }
        when nqp::const::EDGE_SUBRULE {
            die "should never encounter a SUBRULE edge for matching";
        }
        when nqp::const::EDGE_CODEPOINT_I | nqp::const::EDGE_CODEPOINT_I_NEG | nqp::const::EDGE_CODEPOINT_I_LL {
            $v = $v ~~ Int ?? chr($v) !! $v;
            $character ~~ /:i $v /;
        }
        when nqp::const::EDGE_GENERIC_VAR {
            die "should never encounter a GENERIC_VAR edge for matching";
        }
        when nqp::const::EDGE_CHARRANGE | nqp::const::EDGE_CHARRANGE_NEG {
            $character ~~ $v[0]..$v[1];
        }
        when nqp::const::EDGE_CODEPOINT_M | nqp::const::EDGE_CODEPOINT_M_NEG {
            die "action $actname NYI";
        }
        when nqp::const::EDGE_CODEPOINT_M_LL {
            die "action $actname NYI";
        }
        when nqp::const::EDGE_CODEPOINT_IM | nqp::const::EDGE_CODEPOINT_IM_NEG {
            die "action $actname NYI";
        }
        when nqp::const::EDGE_CODEPOINT_IM_LL {
            die "action $actname NYI";
        }
        when nqp::const::EDGE_CHARRANGE_M | nqp::const::EDGE_CHARRANGE_M_NEG {
            die "action $actname NYI";
        }
        default {
            die "didn't have a match for this action??";
        }
    }
    #say "      match result is $result";
    if $negated { $result = not $result }
    return $result;
}

class CClass is rw {
    has $.cclass_id;
    has $.negated;
}
class CRange is rw {
    has $.lower;
    has $.upper;
    has $.negated;
}
# also covers single characters because why not
class CharList is rw {
    has $.chars;
    has $.negated;
}
class Anything is rw {
    has $.negated;
}

sub generate-possible-matching-characters($edge) {
    my $masked_act = $edge[0] +& 0xff;
    my $negated = is-edge-negated($masked_act);
    my $actname = $ACTIONS[$masked_act];
    my $v = $edge[1];
    # say "  does $edge.raku() ($masked_act == $actname) match $character.raku()? (negated? $negated)";
    my $result = do given $masked_act {
        when nqp::const::EDGE_FATE {
            Anything.new()
        }
        when nqp::const::EDGE_EPSILON {
            Anything.new()
        }
        when nqp::const::EDGE_CODEPOINT | nqp::const::EDGE_CODEPOINT_NEG | nqp::const::EDGE_CODEPOINT_LL | nqp::const::EDGE_CHARLIST | nqp::const::EDGE_CHARLIST_NEG {
            CharList.new(chars => ($v ~~ Int ?? chr($v) !! $v));
        }
        when nqp::const::EDGE_CHARCLASS | nqp::const::EDGE_CHARCLASS_NEG {
            # say "    cclass edge";
            CClass.new(cclass_id => $v);
        }
        when nqp::const::EDGE_SUBRULE {
            die "should never encounter a SUBRULE edge for char generation";
        }
        when nqp::const::EDGE_CODEPOINT_I | nqp::const::EDGE_CODEPOINT_I_NEG | nqp::const::EDGE_CODEPOINT_I_LL {
            CharList.new(chars => ($v.lc, $v.uc, $v.fc).Set.list.join(""));
        }
        when nqp::const::EDGE_GENERIC_VAR {
            die "should never encounter a GENERIC_VAR edge for char generation";
        }
        when nqp::const::EDGE_CHARRANGE | nqp::const::EDGE_CHARRANGE_NEG {
            CRange.new(lower => $v[0], upper => $v[1]);
        }
        when nqp::const::EDGE_CODEPOINT_M | nqp::const::EDGE_CODEPOINT_M_NEG {
            die "action $actname NYI";
        }
        when nqp::const::EDGE_CODEPOINT_M_LL {
            die "action $actname NYI";
        }
        when nqp::const::EDGE_CODEPOINT_IM | nqp::const::EDGE_CODEPOINT_IM_NEG {
            die "action $actname NYI";
        }
        when nqp::const::EDGE_CODEPOINT_IM_LL {
            die "action $actname NYI";
        }
        when nqp::const::EDGE_CHARRANGE_M | nqp::const::EDGE_CHARRANGE_M_NEG {
            die "action $actname NYI";
        }
        default {
            die "didn't have a match for this action??";
        }
    }
    $result.negated = $negated;
    return $result;
}

sub split-apart(%splitpoints, $new-edge) {
    my $new = generate-possible-matching-characters($new-edge);

    if $new ~~ CRange {
        %splitpoints{$new.lower} = 1;
        %splitpoints{$new.upper} = 1;
    }
    elsif $new ~~ CharList {
        my @chars = $new.chars.comb.sort;
        # remove entries that have both their predecessor and their successor (in unicode codepoint numbers) in the input as well.
        # TODO this makes no sense with synthetic graphemes, so filter those out.
        my @changepoints = $new.chars.comb.map({
            ($new.chars.contains(chr(ord($_) - 1))
            && $new.chars.contains(chr(ord($_) + 1)))
                ?? Empty !! $_ });

        %splitpoints{$_} = 1 for @changepoints;
    }
    elsif $new ~~ CClass {
        # TODO splitpoints for cclass ...
        # note "don't know yet how to make splitpoints for char class %cclass_names{$new.cclass_id}";
        my $success = 0;
        for ("\n \t\b\a " ~ '-—☺_059abxyzABXYZâẑÂẐßẞſ.,_^[~](){}').comb -> $c {
            if nqp::iscclass($new.cclass_id, $c, 0) {
                %splitpoints{$c} = 1;
                $success++;
            }
        }
        unless $success {
            note "Could not find an example for cclass $new.cclass_id() ($(%cclass_names{$new.cclass_id})) in my silly example string!";
        }
    }
    elsif $new ~~ Anything {
        # no-op
    }
    else {
        note "couldn't handle $new.raku() :(";
    }
}

class NFASimState { ... }

class EdgeId is rw {
    has int $.state-idx;
    has int $.edge-idx;
    has Bool $.epsilon = False;

    method gist {
        "St $.state-idx $($.epsilon ?? "EE" !! "E") $.edge-idx"
    }
}

class SimStateInfo is rw {
    #= Index in the states array (starts at 1, because 0 holds the fates)
    has int $.state-idx;
    #= Edges that matched in the previous state to bring us to this state
    has EdgeId @.preds;
    #= NFASimState that created this state
    has NFASimState $.created-by;

    method gist {
        "State($.state-idx from @.preds.gist())";
    }
}

my $*TRACK-PRED-EDGES = True;

class NFASimState {
    has @.states is rw where $_.elems >= 2;
    has SimStateInfo @.active is rw;
    has str $.text   is rw;
    has int $.offset is rw;
    has $.parent-state is rw;
    has $.nfa-name is rw;
    has $.nfa-basename is rw;

    method gist {
        return {
            states => {
                fates => +@.states[0],
                states => +@.states - 1,
            },
            :@.active,
            :$.text,
            :$.offset,
            parent-state => $.parent-state ?? {
                offset => $.parent-state.offset
            } !! Any,
            :$.nfa-name, :$.nfa-basename,
        }.gist;
    }

    method fork($character) {
        NFASimState.new(
            :@.states, :@.active, text => $.text ~ $character, :parent-state(self), :$.offset, :$.nfa-name, :$.nfa-basename
        );
    }

    multi method start(NFASimState:D: @!states, :$!text = "", :$!offset = 0) {
        @.active = Empty;
        @.active.push(SimStateInfo.new(
            state-idx => 1,
            created-by => self
        ));
        return self;
    }
    multi method start(NFASimState:U: @states, :$text = "", :$offset = 0) {
        return NFASimState.new().start(@states, :$text, :$offset);
    }

    method matching-edges(@edges, $character) {
        my @result;

        # say "get matching edges from ", @edges.rotor(3).list.raku;
        for @edges.rotor(3).pairs {
            if does-edge-match($_.value, $character) {
                # say "matched $_.raku() against $character.raku()";
                @result.push($_);
            }
            else {
                # say "NEGATIVE MATCH: $_.raku() against $character.raku()";
            }
        }

        @result;
    }

    method all-active-edges() {
        my @active-stack = @.active;
        my %seen;
        my @all-edges;
        while @active-stack {
            my $curst = @active-stack.pop;
            my @edges := @.states[$curst.state-idx];
            without %seen{$curst.state-idx} {
                for @edges.rotor(3).pairs {
                    if .value.[0] == nqp::const::EDGE_EPSILON {
                        my $edge-id = EdgeId.new(
                            state-idx => $curst.state-idx,
                            edge-idx  => $_.key,
                            epsilon => True,
                        );

                        @active-stack.push(SimStateInfo.new(
                            state-idx => .value[2],
                            preds =>  $*TRACK-PRED-EDGES ?? (my EdgeId @ = $edge-id) !! [],
                            created-by => self,
                        ));
                    }
                    else {
                        @all-edges.push($_);
                    }
                }
            }
            %seen{$curst.state-idx} = 1;
        }
        @all-edges;
    }

    method step(:$quiet = False --> NFASimState) {
        # get character in question
        my $char = $.text.substr($.offset, 1);
        my $nextst = NFASimState.new(
            :@.states, :$.text, offset => $.offset + 1, parent-state => self, :$.nfa-name, :$.nfa-basename
        );
        my @active-stack = @.active;
        say $char.raku, " with ", +@active-stack, " states    ($(states-key(self)))" unless $quiet;
        my %seen-states;
        my %seen-next-states;
        while @active-stack {
            my $curst = @active-stack.pop;
            my @edges := @.states[$curst.state-idx];
            print("    ", $curst.state-idx, "    ", +@edges, "  ") unless $quiet;
            for @.matching-edges(@edges, $char) -> $ep {
                # TODO implement fate with "to"
                # TODO implement fates and longestlit in general
                my $to = $ep.value[2];

                if $to == 0 {
                    next;
                }

                my $act = $ep.value[0] +& 0xff;

                my $epsilon = $ep.value[0] == nqp::const::EDGE_EPSILON;
                my $edge-id = EdgeId.new(
                    state-idx => $curst.state-idx,
                    edge-idx  => $ep.key,
                    :$epsilon
                );
                print($++ ?? "," !! "", $ep.key, " ", $ACTIONS[$act], "->", $to) unless $quiet;

                # epsilon edges put a new state in our active stack that we will
                # visit real soon, while all other edges are put into the active
                # states array of the next state.
                my $seen-hash := $epsilon ?? %seen-states !! %seen-next-states;
                my $states-array := $epsilon ?? @active-stack !! $nextst.active;

                # Epsilons go on the active stack
                with $seen-hash{$to} -> $seen {
                    if $*TRACK-PRED-EDGES {
                        $seen.preds.push($edge-id);
                    }
                }
                else {
                    $states-array.push(
                        my $new-state = SimStateInfo.new(
                            state-idx => $to,
                            preds => $*TRACK-PRED-EDGES ?? (my EdgeId @ = $edge-id) !! [],
                            created-by => self,
                        )
                    );
                    $seen-hash{$to} = $new-state;
                }
            }
            say("") unless $quiet;
        }

        return $nextst;
    }
}

sub multi-bool-choice-menu(@entries) {
    my @toggles = False xx +@entries;
    loop {
        say "Make your choice...";
        for @entries.pairs {
            say "  ", (@toggles[.key] ?? "[X]" !! "[ ]"), " ", .value.key;
        }
        say "";
        say "number: toggle an entry";
        say "number other third: toggle some entries";
        say "number..* / *..number: toggle from entry to end or beginning to entry";
        say "number..other: toggle range of entries";
        say "  (use ^ before and/or after .. to exclude ends)";
        say "*: toggle all";
        say "r: reset all to Off";
        say "enter: done, accept changes";
        say "q: abort";
        say "";
        my $choice = prompt "Choice: ";
        given $choice {
            when /^ (\d+)+ %% [" " | ","] $/ {
                for @0 {
                    @toggles[+$_] xor= True;
                }
            }
            when /^ $<start>=[ "*" | \d+ ] $<exstart>=["^"?] ".." "."? $<exend>=["^"?] $<end>=[ "*" | \d+ ] $/ {
                my $r = Range.new(
                    $<start> eq "*" ?? 0 !! +$<start>,
                    $<end> eq "*" ?? @toggles.end() !! +$<end>,
                    :excludes-min($<exstart> ne ""),
                    :excludes-max($<exend> ne ""),
                );
                say $r.raku;

                @toggles[@$r] >>[xor=]>> True;
            }
            when /^ "*" $/ {
                @toggles[] >>[xor=]>> True;
            }
            when "r" {
                @toggles >>[=]>> False;
            }
            when "" | "enter" {
                last;
            }
            when "q" {
                return Nil;
            }
            default {
                say "  !!! Unrecognized input $_";
            }
        }
    }

    return (@entries Z @toggles).map({ .[0] if .[1] });
}

sub offer-nfa-choice-from-grammar(Mu $grammar, $filter, :$full_filter = Str) {
    my @methods = Perl6::Grammar.^methods.sort(*.name);

    with $filter {
        my $count-before = +@methods;
        @methods .= grep(*.name.contains($filter));
        if not @methods {
            say "filter $filter.raku() given on commandline matched no methods! There were $count-before methods available.";
        }
    }

    # if we re-run offer-nfa-choice, for example because we changed opt
    # variants, we empty @all-nfas first
    @all-nfas = Empty;

    with $filter {
        say "all NFAs matching $filter.raku():";
    }
    else {
        say "all NFAs:";
    }

    for @methods {
        output-nfas-for-code($_.name, $_, :$full_filter);
    }

    my @entries = do ("  ", .key.fmt("% 3d"), " ", (.value.states.elems - 1).fmt("% 7d"), " states: ", .value.nfa-name).join("") => .value for @all-nfas.pairs;

    my $desired-nfa = do if @all-nfas > 1 {
        my $choice;
        loop {
            .key.say for @entries;
            say "";
            say "s, j: Save NFAs to files (States list or Json)";
            say "q: Abort";

            $choice = prompt "Choice: ";

            if $choice eq "s" | "j" {
                my @choices = multi-bool-choice-menu(@entries);
                my $prefix = ("A".."Z").roll(8).join("");
                my $orig-out = $*OUT;

                for @choices {
                    my $ending = $choice eq "s" ?? "txt" !! "json";
                    my $fname = ("nfa_" ~ $prefix ~ "-" ~ $_.value.nfa-name.subst(" ", "_", :g) ~ "-statelist." ~ $ending).IO;
                    if $choice eq "s" {
                        my $*OUT = $fname.open(:w);
                        mydump(.value.states);
                        $*OUT.close;
                    }
                    else {
                        $fname.spurt(stateslist-to-json(.value.states));
                    }
                    $orig-out.say: "saved $_.key() to $fname.absolute(): $fname.s() bytes";
                }
                say "";
            }
            elsif $choice eq any(@entries.keys) {
                last;
            }
            elsif $choice eq "q" {
                return;
            }
            else {
                say "  !!! Unrecognized input $choice";
            }
        }

        $choice;
    }
    elsif @all-nfas == 1 {
        0;
    }
    else {
        say "got nothing :(";
    }

    my $simstate;

    if $desired-nfa eq any(@all-nfas.keys) {
        my $the-nfa = @all-nfas[$desired-nfa];
        $simstate = NFASimState.start($the-nfa.states, text => '');
        $simstate.nfa-name = $the-nfa.nfa-name;
        $simstate.nfa-basename = $the-nfa.basename;
    }

    return $simstate
}

my %found-states;


my $simstate; 


sub states-key(NFASimState $state) {
    $state.active.map(*.state-idx).sort.join(",");
}

sub generate-futures($state, @spk) {
    my %futures;

    for chr(ord(@spk[0]) - 1), |@spk {
        # say "forking with $_.raku() (", ($state.text ~ $_).raku, ")";
        my $forked = $state.fork($_).step(:quiet);
        my $states-key = states-key($forked);
        %futures{$states-key}.push([$_, $forked]);
        if $forked.text.chars > 1 {
            %found-states{$states-key}.push($forked.text);
        }
    }

    return %futures;
}

sub do-random-exploration(@start-states, :%seen) {
    say " ==> Will automatically explore the NFA's state space.";
    my NFASimState @active = @start-states;

    my $*TRACK-PRED-EDGES = False;

    my $total-added = 0;
    my $longest = 0;

    while @active {
        my NFASimState $item = @active.shift;

        with %seen{states-key($item)} -> $old {
            # say "we already had states for key $(states-key($item)): ", $old.map(*.text.raku).join(", ");
            if $old.elems > 4 {
                next;
            }
            elsif rand < 0.8e0 {
                next;
            }
        }

        my @possible-edges = $item.all-active-edges();
        my %splitpoints;
        @possible-edges.map({ split-apart %splitpoints, $_.value });
        my @spk = %splitpoints.keys.sort;

        if @spk {
            my %futures = generate-futures($item, @spk);

            # randomize order of things picked
            my @suggestions;
            for %futures.pairs.pick(*) -> $f {
                for $f.value.list.pick(*) {
                    @suggestions.push(.[1]);
                }
            }
            @suggestions = @suggestions.unique(as => &states-key);
            @active.push($_) for @suggestions.pick(*);
        }

        $total-added++;
        %seen{states-key($item)}.push($item);
        $longest max= $item.text.chars;

        if $total-added %% 10 {
            say "  ... already seen $total-added.fmt("% 4d") examples for %seen.elems().fmt("% 5d") different states. @active.elems().fmt("% 7d") items in the queue. Longest string $longest";
            @active .= pick(*).sort(-*.text.chars);

            if $total-added >= 500 {
                say " ... aborting search so we don't explode our memory!";
                @active = @active[0];
                last;
            }
        }
    }

    say "Here's all the combinations of states I could find:";
    for %seen.pairs.sort {
        say "States $_.key()";
        say "  ", .value.list.map(*.text.raku()).join(",  ");
        say "";
    }
    say "";

    loop {
        say "s: save to a .json file";
        say "r: pick a random state as the new current state";
        say "c: continue exploring some more";
        say "any other input: do nothing and return to menu";
        say "";
        my $choice = prompt "What do you want to do with it? ";
        if $choice eq "s" {
            my %seen_to_serialize = %seen.pairs.map({ .key => .value.list.map(*.text) });
            my $fn = prompt "filename, please (or press enter for random): ";
            if $fn eq "" {
                my $nfn = ("nfa_exploration_" ~ ("A".."Z").pick(8).join("") ~ ".json").IO;
                say "Saving to $nfn.absolute()";
                $nfn.spurt(to-json(%seen_to_serialize, :pretty));
            }
            elsif $fn.IO.e {
                say "OK to overwrite $fn.IO.absolute() ($fn.IO.s() bytes big)?";
                say "y: yes";
                say "n: no, abort";
                say "r: random new name";
                my $ch2 = prompt "> ";
                if $ch2 eq "y" {
                    $fn.IO.spurt(to-json(%seen_to_serialize, :pretty))
                }
                elsif $ch2 eq "n" {
                    # nothing here
                    next;
                }
                elsif $ch2 eq "r" {
                    my $nfn = ($fn.IO.basename ~ ("A".."Z").pick(8).join("") ~ ".json").IO;
                    say "Saving to $nfn.absolute()";
                    $nfn.spurt(to-json(%seen_to_serialize, :pretty));
                }
            }
            else {
                say " ==> Returning to menu!";
                last;
            }
        }
        elsif $choice eq "r" {
            $simstate = %seen.pairs.pick.value.pick;
            say " ==> Randomly chose this state:";
            say "    $simstate.gist()";
        }
        elsif $choice eq "c" {
            return do-random-exploration(%seen.pairs.map(*.value.Slip).list.grep(*.active > 0), :%seen);
        }
        else {
            say " ==> Returning to menu!";
            last;
        }
    }
}

my $filter = @*ARGS[0];

my Mu $chosen-grammar := Perl6::Grammar;

$simstate = offer-nfa-choice-from-grammar($chosen-grammar, $filter);
main-menu($simstate);

sub main-menu($simstate is copy) {
    while $simstate {
        my @possible-edges = $simstate.all-active-edges();
        # say "possible edges: ", @possible-edges;
        my %splitpoints;
        @possible-edges.map({ split-apart %splitpoints, $_.value });
        my @spk = %splitpoints.keys.sort;

        my @cclasses = @possible-edges
            .map(*.value)
            .map(&generate-possible-matching-characters)
            .grep(CClass)
            .map(*.cclass_id)
            .unique
            .map({ %cclass_names{$_} });

        say "current state: ", $simstate.gist;

        say "";
        say "Current text:";
        say "  ", $simstate.text.raku;
        say "";

        my $should-step = True;

        if $simstate.text.chars <= $simstate.offset || $simstate.active == 0 {
            my @inputs;
            if !@spk || $simstate.active == 0 {
                say "";
                say "The NFA has finished running.";
            }
            elsif @spk {
                say "";
                say "Possible theoretical inputs:";
                say "";

                my %futures = generate-futures($simstate, @spk);

                for %futures.pairs.sort -> $f {
                    my @examples;
                    with %found-states{$f.key} -> $_ {
                        @examples = .grep({ !.starts-with($simstate.text) && .chars != $simstate.text.chars + 1 }).pick(5).map(*.raku);
                    }
                    if @examples {
                        say +@inputs, ": ", $f.key, "    (ex: ", (@examples || Empty).join(", "), ")";
                    }
                    else {
                        say +@inputs, ": ", $f.key;
                    }
                    say "    " ~ $f.value.map(*.[0].raku).join(" ");
                    say "";
                    @inputs.push($f.value[0][0]);
                }

                say " ... also valid: stuff from cclass $_" for @cclasses;
                say "" if @cclasses;

                say "c: Enter your own";
            }

            say "b: go back one";
            say "s: go back to the start";
            say "a: automatically explore";
            say "e: show edges of currently active states";
            say "o: re-do optimization with variants turned on or off";
            say "q: stop";

            my $choice = prompt "Make your choice: ";
            last without $choice;
            if $choice eq "c" {
                my $char = prompt "Which character(s)? ";
                next without $char;
                $simstate .= fork($char);
                say " ==> advancing text: $simstate.text().raku()";
            }
            elsif $choice == any(@inputs.keys) {
                $simstate .= fork(@inputs[$choice]);
            }
            elsif $choice eq "b" {
                $simstate = $simstate.parent-state.parent-state;
                $should-step = False;
                say " ==> Went back one step, text is now $simstate.text().raku()";
            }
            elsif $choice eq "s" {
                $simstate = NFASimState.start($simstate.states);
                $should-step = False;
                say " ==> Returned to start";
            }
            elsif $choice eq "q" {
                say " ==> Quitting ...";
                say "";
                say "Text so far: $simstate.text.raku()";
                last;
            }
            elsif $choice eq "a" {
                do-random-exploration([$simstate]);

                $should-step = False;
            }
            elsif $choice eq "e" {
                mydump($simstate.states, only_states => $simstate.active.map(*.state-idx));
                $should-step = False;
            }
            elsif $choice eq "o" {
                temp $*DEBUG_VERBOSE;
                my $save = False;
                temp &*GET_OPT_OUTPUT;
                loop {
                    say "Available variants:";
                    for @known_variants.pairs {
                        say $_.key, ": ", ($_.value eq any(@*OPT_VARIANTS) ?? "[X]" !! "[ ]"), " ", $_.value;
                    }
                    say "v, vv, vvv: run optimizer with verbosity", ($*DEBUG_VERBOSE > 0 ?? " [$*DEBUG_VERBOSE]" !! "");
                    say "q: run optimizer without output", ($*DEBUG_VERBOSE == 0 ?? " [X]" !! "");
                    say "s: [$($save ?? "X" !! " ")] save optimizer output to files";
                    say "";
                    say "k: accept new variants and re-run optimizer";
                    say "anything else: abort";
                    my $choice = prompt "Choose action: ";
                    if $choice eq any(@known_variants.keys) {
                        if @known_variants[$choice] eq any(@*OPT_VARIANTS) {
                            @*OPT_VARIANTS .= grep(none(@known_variants[$choice]));
                        }
                        else {
                            @*OPT_VARIANTS.push(@known_variants[$choice]);
                        }
                    }
                    elsif $choice eq "k" {
                        my $orig-out = $*OUT;
                        my Pair @output_files;
                        my $prefix = ("A".."Z").roll(8).join("");
                        if $save {
                            &*GET_OPT_OUTPUT = -> Mu $nfa, $variant {
                                with @output_files.tail {
                                    .value.close;
                                    $orig-out.say: "  debugger output in $_.key.absolute(): $_.key.s() bytes";
                                }
                                my $fname = ("nfa_opt_" ~ $prefix ~ "-" ~ $simstate.nfa-name.subst(" ", "_", :g) ~ "-opt-" ~ $variant ~ ".optimize.txt").IO;
                                @output_files.push($fname => my $res = $fname.open(:w));
                                $res;
                            };
                        }
                        my $new = offer-nfa-choice-from-grammar($chosen-grammar, $simstate.nfa-basename, full_filter => $simstate.nfa-name);
                        @output_files.tail.value.close if @output_files;
                        if $save {
                            say "Saved optimizer outputs:";
                            for @output_files {
                                say "  debugger output in $_.key.absolute(): $_.key.s() bytes";
                            }
                        }
                        with $new {
                            $simstate = $new;
                        }
                        else {
                            say " ... No simstate gotten from your previous choice :(";
                        }
                        $should-step = False;
                        last;
                    }
                    elsif $choice eq any(<v vv vvv vvvv>) {
                        $*DEBUG_VERBOSE = $choice.chars;
                        say " ==> Verbosity is now $*DEBUG_VERBOSE";
                    }
                    elsif $choice eq "q" {
                        $*DEBUG_VERBOSE = 0;
                        say " ==> Verbosity is now $*DEBUG_VERBOSE";
                    }
                    elsif $choice eq "s" {
                        $save = not $save;
                    }
                    else {
                        say " ==> Aborting";
                        last;
                    }
                }
            }
            else {
                say "Did not recognize input $choice.raku()";
            }
        }

        if $should-step {
            say "... running step ...";
            $simstate .= step;
            say "";
        }
    }
}
