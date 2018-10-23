#!/usr/bin/env perl

use strict;
use warnings;
use File::Find;
use File::Compare;

$|++;

sub format_haskell_source {
	my $name = $_;
	return unless $name =~ /[.]hs$/;
	# works provided that $name doesn't contain spaces or other metacharacters
	# which it shouldn't anyway.
	system("cabal exec hindent $name > $name.formatted");
	if ((-z "${name}.formatted")) {
		unlink("${name}.formatted");
	}
	elsif (compare($name, "${name}.formatted") == 0) {
		unlink("${name}.formatted");
	} else {
		printf("updating file: %s\n", $name);
		rename(${name}.formatted, $name);
		unlink("${name}.formatted");
	}
}

find(\&format_haskell_source, './src', './test/unit', './test/prop');
