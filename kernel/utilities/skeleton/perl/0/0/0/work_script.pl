#!/usr/bin/perl
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: work_script.pl 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/utilities/skeleton/perl/0/0/0/work_script.pl $
#####################################################################
# Kernel: perl kernel skeleton
#####################################################################

use Getopt::Long;
use DBI;

# this function loads the availiable parameters
GetOptions( 
	"BIMode=s" 				=> \$BIMode,
	"BIProblemSize=s" => \$BIProblemSize
 );

# this sub does the database preparation
sub measurement_init
{
	# initialise the measurement if needed
}

# this sub does the main measurement routine
sub measurement
{
  # do the measurement
}

# build function pointers
%MeasurementModes = (
	'init'     	=> \&measurement_init,
	'read'			=> \&measurement
);

# run measurement or exit
if( $MeasurementModes{ $BIMode } )
{
	$MeasurementModes{ $BIMode }->();
}
else
{
	print "Invalid measurementmode supplied!\n";
}

