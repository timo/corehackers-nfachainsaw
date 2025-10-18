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
            for @states[$s] -> $a, $v, $t {
                my $act = nqp::bitand_i($a,0xff);
                my $action = $ACTIONS[$act];
                if $act == nqp::const::EDGE_CODEPOINT
                  || $act == nqp::const::EDGE_CODEPOINT_LL {
                    say("\t$t $action " ~ nqp::chr($v).raku);
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
                    say("\t$t $action " ~ $v.raku);
                }
                elsif $act == nqp::const::EDGE_SUBRULE
                  && nqp::istype($v,str) {
                    say("\t$t $action " ~ $v.raku);
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


sub my-optimize(Mu $nfa) {
  # say "my optimization yay";
  # say $nfa.states.raku;
  if $nfa.states.elems() > 2 {
    mydump($nfa.states);
  }
  return $nfa;
}

sub my_alt_nfa(Mu $self, Mu $regex, str $name) {
    my Mu $nfa     := $modified_nfa.new;
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

sub my_protoregex_nfa(Mu $self, $name) {
    my $protorx := $self.HOW.cache(
      $self, "!protoregex_table", { $self."!protoregex_table"() }
    );
    my Mu $nfa   := $modified_nfa.new;
    
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
      say $indent ~ "     instantiated: " ~ recursive-hllize($alt_nfa.states).raku;
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

for Perl6::Grammar.^methods.sort(*.name) {
  output-nfas-for-code($_.name, $_);
}
