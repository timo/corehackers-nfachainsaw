unit module CoreHackers::NfaChainsaw::Utils::UserInterface;

our sub prompt(\c) {
    my $res := &CORE::prompt(|c);
    if $*IN.eof {
        die "User closed the input stream";
    }
    $res;
}

sub multi-bool-choice-menu(@entries) is export {
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
