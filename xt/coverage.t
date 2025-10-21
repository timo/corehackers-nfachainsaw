use Code::Coverage;
use Test::Coverage;

plan 2;

default-coverage-setup;

# Exclude User Interface utilities code for now.
my $own-coverage = Code::Coverage.new(
    targets => $*CODE-COVERAGE.targets.grep(none("CoreHackers::NfaChainsaw::Utils::UserInterface")),
    runners => $*CODE-COVERAGE.runners,
    extra => $*CODE-COVERAGE.extra,
    repo => $*CODE-COVERAGE.repo,
    tmpdir => $*CODE-COVERAGE.tmpdir,
    slug => $*CODE-COVERAGE.slug,
);

given $own-coverage -> $*CODE-COVERAGE {
    run;

    todo "write simple tests for everything";
    coverage-at-least 90;

    todo "write many more tests";
    uncovered-at-most 50;

    source-with-coverage;

    report;
}
