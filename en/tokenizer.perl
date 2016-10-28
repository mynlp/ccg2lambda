#!/usr/bin/perl -w

# Sample Tokenizer
# written by Josh Schroeder, based on code by Philipp Koehn

binmode(STDIN, ":utf8");
binmode(STDOUT, ":utf8");
use strict;

my %NONBREAKING_PREFIX = ();
my $language = "en";
my $QUIET = 0;
my $HELP = 0;

while (@ARGV) {
	$_ = shift;
	/^-l$/ && ($language = shift, next);
	/^-q$/ && ($QUIET = 1, next);
	/^-h$/ && ($HELP = 1, next);
}

if ($HELP) {
	print "Usage ./tokenizer.perl (-l [en|de|...]) < textfile > tokenizedfile\n";
	exit;
}
if (!$QUIET) {
	print STDERR "Tokenizer Version 1.0\n";
	print STDERR "Language: $language\n";
}

load_prefixes($language,\%NONBREAKING_PREFIX);

if (scalar(%NONBREAKING_PREFIX) eq 0){
	print STDERR "Warning: No known abbreviations for language '$language'\n";
}

while(<STDIN>) {
	if (/^<.+>$/ || /^\s*$/) {
		#don't try to tokenize XML/HTML tag lines
		print $_;
	}
	else {
		print &tokenize($_);
	}
}

sub tokenize {
	my($text) = @_;
	chomp($text);
	$text = " $text ";
	
	# seperate out all "other" special characters
	$text =~ s/([^\p{IsAlnum}\s\.\'\`\,\-])/ $1 /g;
	
	#multi-dots stay together
	$text =~ s/\.([\.]+)/ DOTMULTI$1/g;
	while($text =~ /DOTMULTI\./) {
		$text =~ s/DOTMULTI\.([^\.])/DOTDOTMULTI $1/g;
		$text =~ s/DOTMULTI\./DOTDOTMULTI/g;
	}

	# seperate out "," except if within numbers (5,300)
	$text =~ s/([^\p{IsN}])[,]([^\p{IsN}])/$1 , $2/g;
	# separate , pre and post number
	$text =~ s/([\p{IsN}])[,]([^\p{IsN}])/$1 , $2/g;
	$text =~ s/([^\p{IsN}])[,]([\p{IsN}])/$1 , $2/g;
	      
	# turn `into '
	$text =~ s/\`/\'/g;
	
	#turn '' into "
	$text =~ s/\'\'/ \" /g;

	if ($language eq "en") {
		#split contractions right
		$text =~ s/([^\p{IsAlpha}])[']([^\p{IsAlpha}])/$1 ' $2/g;
		$text =~ s/([^\p{IsAlpha}\p{IsN}])[']([\p{IsAlpha}])/$1 ' $2/g;
		$text =~ s/([\p{IsAlpha}])[']([^\p{IsAlpha}])/$1 ' $2/g;
		$text =~ s/([\p{IsAlpha}])[']([\p{IsAlpha}])/$1 '$2/g;
		#special case for "1990's"
		$text =~ s/([\p{IsN}])[']([s])/$1 '$2/g;
	} elsif ($language eq "fr") {
		#split contractions left	
		$text =~ s/([^\p{IsAlpha}])[']([^\p{IsAlpha}])/$1 ' $2/g;
		$text =~ s/([^\p{IsAlpha}])[']([\p{IsAlpha}])/$1 ' $2/g;
		$text =~ s/([\p{IsAlpha}])[']([^\p{IsAlpha}])/$1 ' $2/g;
		$text =~ s/([\p{IsAlpha}])[']([\p{IsAlpha}])/$1' $2/g;
	} else {
		$text =~ s/\'/ \' /g;
	}
	
	# . abbreviator / end of sentence 
	my $t = "";
	$text =~ s/\s+/ /g;
	while ($text =~ /.+?(\S+)\. +(\S+)( *.*)$/) {
		my $pre = $1; 
		my $post = $2; 
		my $rest = $3;
		my $skipped = substr($text,0,length($text)-2-length($pre.$post.$rest));
		if ($pre =~ /\./ || $NONBREAKING_PREFIX{$1} || $post =~ /^[\p{IsLower}]/) {	# next word is lowercase
			$t .= $skipped.$pre.". ";
		}
		else {
			$t .= $skipped.$pre." . ";
		}
		$text = $post.$rest;
	}
	
	#clean up last piece
	$text = $t . $text;
	$text =~ s/\. *$/ ./;

	# clean up extraneous spaces
	$text =~ s/ +/ /g;
	$text =~ s/^ //g;
	$text =~ s/ $//g;

	#restore multi-dots
	while($text =~ /DOTDOTMULTI/) {
		$text =~ s/DOTDOTMULTI/DOTMULTI./g;
	}
	$text =~ s/DOTMULTI/./g;
	
	#ensure final line break
	$text .= "\n" unless $text =~ /\n$/;

	return $text;
}

sub load_prefixes {
	#create a hash, with value 1, for any titles or abbreviations we want to not break
	my ($lang, $PREFIX_REF) = @_;
	if (($language eq "en") or ($language eq "es") or ($language eq "de") or ($language eq "fr")) {
		#generic cases for basic latin/european languages
		my @BASIC_PREFIXES = ("Adj","Adm","Adv","Asst","Ave","Bldg","Brig","Bros","Capt","Cmdr","Col","Comdr",
				      "Con","Corp","Cpl","Dr","Ens","Gen","Gov","Hon","Hosp","Insp","Lt","Maj",
				      "Messrs","Mlle","Mme","Mr","Mrs","Ms","Msgr","Op","Ord","Pfc","Ph","Prof","Pvt",
				      "Rep","Reps","Res","Rev","Rt","Sen","Sens","Sgt","Sr","St","Supt","Surg","v","vs",
				      "A","B","C","D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V","W","X","Y","Z");
		foreach my $prefix (@BASIC_PREFIXES) {
			$PREFIX_REF->{$prefix} = 1;
		}
	}
	if ($language eq "de") {
		#In german, IV. and 3. December contain dots we don't want to abbreviate for
		my @GERMAN_PREFIXES = ("II","III","IV","VI","VII","VIII","IX","Mio","Mrd","bzw");
		#Add all numbers 1-99
		for (my $i=1;$i<100;$i++) {
			push(@GERMAN_PREFIXES,"".$i);	
		}
		foreach my $prefix (@GERMAN_PREFIXES) {
			$PREFIX_REF->{$prefix} = 1;
		}
	}
} 	

