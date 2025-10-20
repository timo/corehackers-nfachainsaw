unit module CoreHackers::NfaChainsaw::Optimizer;


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
