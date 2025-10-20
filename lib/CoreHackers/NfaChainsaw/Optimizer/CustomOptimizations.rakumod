use nqp;

unit module CoreHackers::NfaChainsaw::Optimizer::CustomOptimizations;

sub CUSTOM_steal_edges_from_all_states_epsilon_reachable_from_start(@states, @incoming) is export {
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
