#!/usr/bin/env rakudo
use nqp;
use Perl6::Grammar:from<NQP>;
use QRegex:from<NQP>;

sub recursive-hllize(Mu $in) {
  my $h = nqp::hllize($in);
  if $h ~~ Positional {
    my @result = do recursive-hllize($_).item for @$h;
    return @result;
  }
  elsif $h ~~ Hash {
      die "ack";
  }
  else {
      return $h;
  }
}

my $match = Perl6::Grammar.new;

my Mu $protoregex_meth := $match.^find_method("!protoregex_table");

my Mu $qregex_nfa_class := QRegex::NFA;

my $modified_nfa = $qregex_nfa_class but role { method optimize { return my-optimize(self); } }

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
  'EDGE_CODEPOINT_M_LL',
  'EDGE_CODEPOINT_IM',
  'EDGE_CODEPOINT_IM_NEG',
  'EDGE_CODEPOINT_IM_LL',
  'EDGE_CHARRANGE_M',
  'EDGE_CHARRANGE_M_NEG'
];



sub mydump(@states) {
    my int $send = +@states;
    if $send > 1 {
        say("==========================================\n   $send states");
        say("Fates:");
        for @states[0] -> $f {
            $f = "" if nqp::isnull($f);
            say("\t$f");
        }
        say("");
        my int $s = 1;
        while $s < $send {
            say("$s:");
            for @states[$s].list -> $a, $v, $t {
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
                else {
                    say("\t$t $action");
                }
            }
            say("");
            $s++;
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

  for 1..^@states {
    if @remap[$_] {
      say("\t$_ -> @remap[$_]");
    }
  }

  say("\n\nnow @states.elems() states before unlinking empties\n");

  say (now - ENTER now), "  remapping has @remap.grep(none(0)).elems() elements";

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
          say "  chasing $was to $newto";
        }

        if $newto != $to {
          @state[$e] = $newto;
        }

        @incoming[$newto]++;
      }
      $e += 3;
    }
  }

  mydump(@states);

  say("\n\nnow @states.elems() states before stealing singleton edges\n");

  say (now - ENTER now), "  cleared $cleared states, followed the mapping $chased steps";
  return @incoming;
}


sub CUSTOM_steal_edges_from_all_states_epsilon_reachable_from_start(@states, @incoming) {
  my $removed = 0;
  my int @work = 1;
  my int @seen;

  my @newedges;
  my @oldedges = @states[1].list;

  say "start state edges: ", @oldedges.raku;

  while @work {
    my $item = @work.pop;

    next if @seen[$item]++;

    say "    considering state $item for edge stealing;";

    my @state := @states[$item];
    say "      states: @state[]";

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
        say "      epsilon!";
        @work.push($to);
      }
      else {
        my $v = @state[$e - 1];
        say "      $ACTIONS[$act]!";
        @newedges.push(@state[$e - 2]);
        @newedges.push($v);
        @newedges.push($to);
      }

      $e += 3;
    }

    #if $was_removed {
    #  say "clearing out state $item";
    #  @states[$item] := [];
    #}
  }

  @states[1] = @newedges;
  
  say (now - ENTER now), "  removed $removed states after stealing edges from stuff reachable with epsilon from start state.";
  say "    @seen.grep(* != 0).elems() states in the epsilon-closure of state 1:  @seen.pairs().grep(*.value != 0).map(*.key)";
  say "    state 1 used to have @oldedges.elems() elements, now has @newedges.elems()";
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

          say "  $stateidx stealing $to";

          @state[$e - 2] = $tostate[0];
          @state[$e - 1] = $tostate[1];
          @state[$e    ] = $tostate[2];
  
          if --@incoming[$to] == 0 {
            say "    clearing out unused state $to";
            @states[$to] = [];
            $removed++;
          }
        }
      }
      $e += 3;
    }
  }

  say("\n\nnow @states.elems() states before calculating remap\n");

  say (now - ENTER now), "  removed $removed states that were no longer referenced.";
}

sub ORIG_resequence_states_to_skip_empty(@states) {
  my @remap;
  my $newend = 0;
  for 1..^@states {
    @remap[$_] = (@states[$_].elems == 0 ?? 0 !! ++$newend);
  }

  say("\n\nnow @states.elems() states\n");

  mydump(@states);
  for 1..^@states {
    if @remap[$_] {
      say("\t$_ -> @remap[$_]");
    }
  }

  say("\n\nnow @states.elems() states mapping to $newend states\n");

  say (now - ENTER now), "  remapping has @remap.grep(none(0)).elems() elements";
  say "  new length of state array is $newend, was @states.elems()";

  return @remap;
}

sub ORIG_move_states_for_resequence(@states, @remap) {
  my @newstates;
  @newstates[0] = @states[0];

  my $dups_deleted = 0;

  for 1..^@states {
    my $s = $_;
    my @state := @states[$_];
    say "Skipping $_" if @state == 0;
    next if @state == 0;
    my $newpos = @remap[$_];

    if $newpos {
      say "state $newpos is a clone of state $_";

      my int $eend = +@state;
      my int $e = 2;
      while $e < $eend {
        my $to = @state[$e];
        my $act = @state[$e - 2] +& 0xff;

        if $to {
            @state[$e] = @remap[$to];
            say "In $s -> $newpos remapping $ACTIONS[$act] $to -> @remap[$to]";
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
              say("Deleting dup edge at $s $e/$f");
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



  say (now - ENTER now), "  deleted $dups_deleted duplicate edges";
  @newstates;
}

class HLLNFA {
  has @.states is rw;
  method save { @.states }
}

sub my-optimize(Mu $nfa) {
  my @states = recursive-hllize($nfa.states);

  if @states <= 2 { return HLLNFA.new(:@states) }

  say "BEGIN OF OPTIMIZATION";

  #dd :@states;
  mydump(@states);

  my @remap = ORIG_find_single_epsilon_states(@states);

  mydump(@states);

  #dd :@remap;

  my @incoming = ORIG_clear_remapped_and_count_incoming(@states, @remap);

  #dd :@states, :@incoming;
  #dd :@states;

  ORIG_steal_from_single_edge_states_behind_epsilon(@states, @incoming);

  #dd :@states;

  # dd :@states;

  my @resequence = ORIG_resequence_states_to_skip_empty(@states);
  # dd :@resequence;

  #mydump(@states);

  @states = ORIG_move_states_for_resequence(@states, @resequence);

  mydump(@states);

  #CUSTOM_steal_edges_from_all_states_epsilon_reachable_from_start(@states, @incoming);

  say "END OF OPTIMIZATION";

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


sub output-nfas-for-code($name, Mu $m, $indent = "   ") {
  say $indent ~ " name: " ~ $_ with $name;
  say "$indent   raw NFA: ", nqp::hllize($_).raku with $m.?NFA;

  if $m.?ALT_NFAS {
    my %alt_nfas := nqp::hllize($m.ALT_NFAS);
    for %alt_nfas {
      say "$indent   $_.key(): " ~ recursive-hllize($_.value()).raku;
  
      my $alt_nfa := my_alt_nfa($match, $m, $_.key);
      my @states := recursive-hllize($alt_nfa.states);
      say $indent ~ "     instantiated: " ~ @states.raku;

      if @states > 2 {
        {
          my $*OUT = "/tmp/optimizer.$($_.key).ported.txt".IO.open(:w);
          mydump(@states);
          $*OUT.close;
        }

        {
          my $*OUT = "/tmp/optimizer.$($_.key).orig.txt".IO.open(:w);
          my $protoregex_nfa := my_alt_nfa($match, $m, $_.key, QRegex::NFA);
          if $protoregex_nfa.save != 0 {
            mydump($protoregex_nfa.save);
          }
          $*OUT.close;
        }
      }
      
    }
  }
  
  if $m.?NESTED_CODES.DEFINITE {
    for 0..* Z nqp::hllize($m.NESTED_CODES) -> ($idx, $c) {
      output-nfas-for-code($name ~ "[" ~ $idx ~ "]", $c, $indent ~ "  ");
    }
  }

  my $protoregex_nfa := my_protoregex_nfa($match, $m.name);
  my $saved := $protoregex_nfa.save;
  my @states = @$saved;

  if @states > 2 && @states[0] != 0 && @states[1] != 0 {
    say $indent ~ " instantiated protoregex_nfa: " ~ @states.raku;
  }
}

for Perl6::Grammar.^methods.sort(*.name)
#  .grep(*.name eq "termish")
{
  output-nfas-for-code($_.name, $_);
}

