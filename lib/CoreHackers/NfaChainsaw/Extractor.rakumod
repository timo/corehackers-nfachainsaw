use nqp;
use Perl6::Grammar:from<NQP>;
use QRegex:from<NQP>;

my $match = Perl6::Grammar.new;

my Mu $protoregex_meth := $match.^find_method("!protoregex_table");

my Mu $qregex_nfa_class := QRegex::NFA;

my $modified_nfa = $qregex_nfa_class but role { method optimize { return my-optimize(self); } }


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
        @*all-nfas.push(NFAFromGrammar.new(nfa-name => $thename, states => @states, basename => $basename_for_regen));
        say $indent ~ "     instantiated $thename: " ~ @states.raku;
      }
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
      @*all-nfas.push(NFAFromGrammar.new(nfa-name => ($thename ~ " protoregex"), states => @states, basename => $basename_for_regen));
      say $indent ~ " instantiated protoregex_nfa: " ~ @states.raku;
    }
  }
}

