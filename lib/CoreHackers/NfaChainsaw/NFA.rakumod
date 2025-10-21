unit module CoreHackers::NfaChainsaw::NFA;

use nqp;

use JSON::Fast;

sub recursive-hllize(Mu $in) is export {
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

our sub stateslist-to-json(@states) is export {
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

our $ACTIONS = [
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

our %cclass_names = (
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

our sub dump_state($s, @edges) {
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

our sub mydump(@states, :@only_states) is export {
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

our class HLLNFA is export {
  has @.states is rw;
  method save { @.states }
  method dump(:@only_states) { mydump(:@only_states) }
}
