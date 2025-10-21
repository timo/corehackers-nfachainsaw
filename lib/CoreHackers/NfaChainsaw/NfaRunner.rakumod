unit module CoreHackers::NfaChainsaw::NfaRunner;

use nqp;

use CoreHackers::NfaChainsaw::NFA;

my $ACTIONS := $CoreHackers::NfaChainsaw::NFA::ACTIONS;
my %cclass_names := %CoreHackers::NfaChainsaw::NFA::cclass_names;

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

class CClass is rw is export {
    has $.cclass_id;
    has $.negated;
}
class CRange is rw is export {
    has $.lower;
    has $.upper;
    has $.negated;
}
# also covers single characters because why not
class CharList is rw is export {
    has $.chars;
    has $.negated;
}
class Anything is rw is export {
    has $.negated;
}

sub generate-possible-matching-characters($edge) is export {
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

sub split-apart(%splitpoints, $new-edge) is export {
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

class EdgeId is rw is export {
    has int $.state-idx;
    has int $.edge-idx;
    has Bool $.epsilon = False;

    method gist {
        "St $.state-idx $($.epsilon ?? "EE" !! "E") $.edge-idx"
    }
}

class SimStateInfo is rw is export {
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


sub states-key(NFASimState $state) {
    $state.active.map(*.state-idx).sort.join(",");
}


class NFASimState is export {
    has @.states is rw where $_.elems >= 2;
    has SimStateInfo @.active is rw;
    has str $.text   is rw;
    has int $.offset is rw;
    has $.parent-state is rw;
    has $.nfa-name is rw;
    has $.nfa-basename is rw;

    method states-key() {
        states-key(self);
    }

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
