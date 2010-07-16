#!/opt/local/bin/perl

use WWW::NicoVideo::Download;

print "Loading NicoVideo...\n";

my $password = $ARGV[0];

my $client = WWW::NicoVideo::Download->new(
 email => "jay.mccarthy\@gmail.com",
 password => $password );

my $video_id = $ARGV[1];
my $filename = $ARGV[2];

print "Downloading $video_id\n";

$client->download($video_id, $filename);
