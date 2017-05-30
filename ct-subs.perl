#!/usr/bin/perl
#
#	ct:	a prototype "C with tuples" to C translator..
#
#		In LinkedIn's Plain Old C Programming group, Rick Marshall asked about why Tuples
#		aren't implemented in C.  As an experiment, I wondered whether we could
#		graft tuple-returning functions into C via a pre-processor,
#		looking for, checking and modifying special %proto, %func, %return and %call lines.
#
#	(C) May 2017, Duncan C. White
#
# As a start, forget %proto, just implement:
#
#	%func static (int, int, char *) fred( double a );
#	%return ( 3, 5, "hello" );
#	%call (int x, int y, char *string ) = fred( 9.5 );
#
#	Note that various semantic checks could be made too:
#	
#	- when a %func line is parsed, assert( ! already known ), then
#	  add fred -> ( static function taking double and returning int, int, char *
#	  would be added to %tuple-func-info.  also current-function would be set to fred.
#	
#	- when a %return line is parsed, first we would check that current-function is set, and
#	  retrieve current-function's type signature from %tuple-func-info, and then we would check
#	  that there are the correct number of values.  as these are full blown C expressions, unless
#	  we build a serious parser we can't check the type of the values.
#	
#	- when a %call line is parsed, we'd check that the function is present in %tuple-func-info (meaning
#	  that a %func definition has been seen for that function), then we'd retrieve the type signature,
#	  then we'd check that there were the right number of parameters - expressions again, so
#	  count-checking only - and check that the tuple destructor matched the return type.

use strict;
use warnings;
use 5.010;
use Data::Dumper;


my %tupfuncinfo;	# hash from tuple-function name -> type signature, including static


#
# my @returntype = parsetupletype( $tuple );
#	Parse a '(' list( simpletype, ',') ')' tuple type from $tuple,
#	where simpletype is no more complex than int. int *, int *******..
#	build an array of simpletype strings, and return it.
#
sub parsetupletype
{
	my( $tuple ) = @_;
	#print "debug: parsing tuple type from $tuple\n";
	$tuple =~ s/^\s+//;
	$tuple =~ s/^\s+//;
	my @result;
	# a simpletype is something like int, int *, int **** etc.
	while( $tuple =~ s/^(\w+)\s*([*]*)// )
	{
		push @result, $2?"$1 $2":$1;
		$tuple =~ s/\s*,\s*//;
	}
	return @result;
}


#
# my @params = parseparams( $line );
#	Parse a list( simpletype id, ',') of parameters from $line,
#	build an array of "simpletype id" strings, and return it.
#
sub parseparams
{
	my( $line ) = @_;
	#print "debug: parsing params from $line\n";
	my @result;
	# a param is something like int p, int *p, int ****p etc.
	while( $line =~ s/^(\w+)\s+([*]*)\s*(\w+),?\s*// )
	{
		push @result, "$1 $2$3";
	}
	return @result;
}


my $lineno = 1;		# current line no inside input source file
my $currfunc;		# name of current function..
my $indent;		# current line's leading whitespace (removed from line)


#
# fatal( $stat, @msg );
#	Given a statement $stat, and an array of messages @msg, print
#	a standard-formatted fatal error and die.  uses $indent and $lineno.
#
sub fatal
{
	my( $stat, @msg ) = @_;
	my $err = "${indent}$stat\n";
	my $m = shift @msg;
	$err .= "$indent^ Error at line $lineno: $m\n";
	foreach my $m (@msg)
	{
		$err .= "$indent  $m\n";
	}
	die "$err";
}


#
# my $altered = parse_func( $line );
#	Given a %func line (%func already removed), parse a function,
#	record it's tuple function info, and return the altered normal C line.
#
sub parse_func
{
	my( $line ) = @_;
	my $origline = $line;

	my $static = 0;
	$static++ if $line =~ s/^static\s+//;
	$line =~ s/^\(([^\)]+)\)\s*//;
	my $tuple = $1;
	my @returntype = parsetupletype( $tuple );

	$line =~ s/^(\w+)\s*//;
	my $funcname = $1;
	$line =~ s/^\(\s*//;
	$line =~ s/\s*\)$//;

	# line now contains only the parameters.
	my $params = $line;
	my @params = parseparams( $line );

	# check that $funcname is not already defined..
	my $info = $tupfuncinfo{$funcname};
	if( $info )
	{
		fatal( $origline, "Function $funcname already defined" ) if $info->{DEFINED};
	}

	$info = {
		STATIC => $static,
		FUNCNAME => $funcname,
		RETURNTYPE => \@returntype,
		RETURNTUPLE_STR => $tuple,
		PARAMS => \@params,
		ORIGLINE => $origline,
		DEFINED => 1,
	};
	#print Dumper $info;
	$tupfuncinfo{$funcname} = $info;

	$currfunc = $funcname;

	my $altered = "";
	$altered = "static " if $static;
	my @x = @returntype;
	my $returntype = shift @x;
	$params .= ', ' . join( ', ', map { "$x[$_] *_tp$_" } 0..$#x );
	$altered .= "$returntype $funcname( $params )";
	return $altered;
}


#
# my $altered = parse_return( $line );
#	Given a %return line (%return already removed), parse a return tuple,
#	check the current function's return type against the number of elements in
#	the return tuple, and return the altered normal C line.
#
sub parse_return
{
	my( $line ) = @_;
	my $origline = "%return $line";

	fatal( $origline, "return not inside a function" ) unless $currfunc;

	my $info = $tupfuncinfo{$currfunc};
	die "ct: logic-error: return $line inside function $currfunc, missing from %tfi\n"
		unless $info;
	my $ret = $info->{RETURNTYPE};
	my $origfunc = $info->{ORIGLINE};
	my @r = @$ret;
	my $nr = @r;

	my $origreturn = "% return $line";
	#print "debug: parsing return $line\n";
	$line =~ s/^\(\s*//;
	$line =~ s/\s*\)\s*;$//;
	#print "debug: parsing return $line\n";

	my @args = split( /,/, $line );			# WON'T HANDLE "hello, there" well..
	my $na = @args;

	fatal( $origline, "wrong number of elements ($na) in return",
		"$origfunc returns $nr elements" ) unless $na == $nr;

	my $rettype = shift @r;
	my $first = shift @args;
	my $altered = join( '; ', map { "*_tp$_ = $args[$_]" } 0..$#r );
	$altered .= "; return $first;    // $origreturn";
	return $altered;
}


#
# my @pieces = parsetupleassign( $tuple );
#	Given a tuple assignment in $tuple, eg "int x, int y",
#	parse it, return a list of variable declarations.
#
sub parsetupleassign
{
	my( $tuple ) = @_;
	#print "debug: parsing tuple assignment from $tuple\n";
	$tuple =~ s/^\s+//;
	$tuple =~ s/^\s+//;
	my @result;
	# a variable decln is something like int x, int *y, int ****z etc.
	while( $tuple =~ s/^(\w+)\s*([*]*)\s*(\w+)// )
	{
		push @result, $2?"$1 $2$3":"$1 $3";
		$tuple =~ s/\s*,\s*//;
	}
	my $nt = @result;
	#print "debug: having parsed tuple assignment, $nt pieces, $tuple left over\n";
	return @result;
}


#
# my $altered = parse_call( $line );
#	Given a %call line (%call already removed), parse it, check it against
#	the %func definition, and then return a string of normal C code.
#	syntax '(' tuple-assign ')' = funcname '(' args ')'
#
#
sub parse_call
{
	my( $line ) = @_;
	my $origline = "%call $line";

	#print "debug: parsing %call $line\n";

	$line =~ s/^\(([^\)]+)\)\s*//;
	my $tuple = $1;
	my @pieces = parsetupleassign( $tuple );
	my $npieces = @pieces;
	#print Dumper \@pieces;
	my $vars = join( '; ', @pieces );

	# just the variable names..
	my @varnames = map { /(\w+)$/ && $1 } @pieces;
	#print Dumper \@varnames;

	# just the types..
	my @tfp = map { /[*]/ ? ( /^(\w+\s*[*]+)/ ) : (/^(\w+)/ ); $1  } @pieces;
	#print Dumper \@tfp;

	#print "debug: after parsing tuple assign, tuple=$tuple, $npieces pieces, vars $vars, line=$line\n";
	$line =~ s/^=\s*(\w+)\s*//;
	my $funcname = $1;
	$line =~ s/^\(\s*//;
	$line =~ s/\s*\)\s*;$//;

	#print "debug: funcname = $funcname, left = $line\n";

	my @args = split( /,/, $line );			# WON'T HANDLE "hello, there" well..
	my $na = @args;
	#print "debug: $na args ($line)\n";
	my $args = join( ',', @args );

	my $info = $tupfuncinfo{$funcname};
	fatal( $origline, "No such tuple function $funcname" ) unless $info;

	my $params = $info->{PARAMS};
	my $ret = $info->{RETURNTYPE};
	my $origfunc = $info->{ORIGLINE};
	my @r = @$ret;
	my $nr = @r;

	my @p = @$params;	# formal parameters
	my $np = @p;

	#print "debug: func $funcname has $np params, $na actual, $nr-tuple return type, $npieces pieces\n";

	fatal( $origline, "wrong number of actual parameters ($na)",
		"$origfunc has $np formal parameters" ) unless $np == $na;

	fatal( $origline, "wrong number of tuple-pieces ($npieces)",
		"$origfunc returns an $nr-tuple" ) unless $npieces == $nr;

	# check each element of the NR-tuple return type
	foreach my $pos (0..$#r)
	{
		fatal( $origline,
			"$pieces[$pos] in return tuple should be $r[$pos]" )
				unless $r[$pos] eq $tfp[$pos];
	}

	my $altered = $vars;
	$altered .= "; ";

	# first piece of tuple is special.
	my $firstvarname = shift @varnames;
	$args .= ', ' . join( ', ', map { "&$_" } @varnames );
	$altered .= "$firstvarname = $funcname( $args );\t// $origline";

	return $altered;
}


#
# my $altered = rewrite( $line );
#	Given a specially marked %C-with-tuples line $line, parse it, check it, and
#	return the altered "line" to be printed.
#
sub rewrite
{
	my( $line ) = @_;
	$line =~ s/^\s+//;
	$line =~ s/\s+$//;
	if( $line =~ s/^func\s+// )	# %func [static] tuple-type funcname '(' params ')'
	{
		return parse_func( $line );
	} elsif( $line =~ s/^return\s*// )	# %return '(' values ')'
	{
		return parse_return( $line );
	} elsif( $line =~ s/^call\s+// )	# %call tuple-assign = funcname '(' args ')'
	{
		return parse_call( $line );
	}
	return $line;
}



die "Usage: ct name-of-CT-file name-of-generated-C-file\n" unless @ARGV == 2;
my $ctfilename = shift;
my $cfilename = shift;

open( my $infh, '<', $ctfilename ) || die "ct: can't open $ctfilename\n";
open( my $outfh, '>', $cfilename ) || die "ct: can't create $cfilename\n";
while( <$infh> )
{
	chomp;
	if( s/^(\s*)%(\s*)// )
	{
		$indent = $1.$2;
		$_ = $indent . rewrite($_);
	}
	print $outfh "$_\n";
	$lineno++;
}
close( $infh );
close( $outfh );

system( "gcc -Wall $cfilename" ) == 0 || die "ct: errors compiling $cfilename\n";

system( "./a.out" );
