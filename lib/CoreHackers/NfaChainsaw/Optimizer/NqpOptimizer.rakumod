use nqp;

unit module CoreHackers::NfaChainsaw::Optimizer::NqpOptimizer;

sub ORIG_find_single_epsilon_states(@states) is export {
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

sub ORIG_clear_remapped_and_count_incoming(@states, @remap) is export {
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


sub ORIG_steal_from_single_edge_states_behind_epsilon(@states, @incoming) is export {
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

sub ORIG_resequence_states_to_skip_empty(@states) is export {
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

sub ORIG_move_states_for_resequence(@states, @remap) is export {
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
