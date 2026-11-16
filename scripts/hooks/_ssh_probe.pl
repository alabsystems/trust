# Bounded ssh -G capture. Invoked with Perl by _ssh_keepalive.sh, never as a
# transport. Perl and these core modules are available on macOS and Linux.
#
# The child leads a new session. Keep it unreaped until the LAST group signal:
# its reserved PID then prevents that PGID being reused for an unrelated job.
# SIGCHLD observes termination without waitpid; SA_NOCLDSTOP excludes stops.
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
use strict;
use warnings;
use Errno qw(EAGAIN EINTR ESRCH);
use Fcntl qw(F_GETFL F_SETFL O_NONBLOCK);
use IO::Select;
use POSIX qw(setsid sigaction SIGCHLD SA_NOCLDSTOP WNOHANG);
use Time::HiRes qw(clock_gettime CLOCK_MONOTONIC sleep);

shift @ARGV if @ARGV && $ARGV[0] eq '--';
exit 2 unless @ARGV;
my ($done, $stop) = (0, 0);
my %signals = (HUP => 1, INT => 2, QUIT => 3, TERM => 15);
for my $name (keys %signals) {
    $SIG{$name} = sub { $stop ||= $signals{$name}; };
}
$SIG{PIPE} = sub { $stop ||= 13; };
sigaction(SIGCHLD, POSIX::SigAction->new(sub { $done = 1 },
    POSIX::SigSet->new(), SA_NOCLDSTOP)) or exit 2;
pipe(my $out_r, my $out_w) or exit 2;
pipe(my $ready_r, my $ready_w) or exit 2;
pipe(my $ack_r, my $ack_w) or exit 2;
my $pid = fork();
exit 2 unless defined $pid;
if (!$pid) {
    for my $name (keys %signals, 'PIPE', 'CHLD') { $SIG{$name} = 'DEFAULT'; }
    close $out_r; close $ready_r; close $ack_w;
    my $session = setsid();
    defined($session) && $session == $$ && getpgrp() == $$ or POSIX::_exit(127);
    # No command can run before the parent knows this group belongs to it.
    syswrite($ready_w, '1') == 1 or POSIX::_exit(127);
    close $ready_w;
    my $ack = '';
    sysread($ack_r, $ack, 1) == 1 && $ack eq '1' or POSIX::_exit(127);
    close $ack_r;
    open(STDOUT, '>&', $out_w) or POSIX::_exit(127);
    close $out_w;
    exec { $ARGV[0] } @ARGV or POSIX::_exit(127);
}
close $out_w; close $ready_w; close $ack_r;
my $flags = fcntl($out_r, F_GETFL, 0);
my $failed = !defined($flags) || !defined(fcntl($out_r, F_SETFL, $flags | O_NONBLOCK));
my ($owned_group, $eof, $output) = (0, 0, '');
my $select = IO::Select->new($out_r, $ready_r);
my $deadline = clock_gettime(CLOCK_MONOTONIC) + 10;
while (!$stop && !$failed && !($done && $eof)) {
    my $left = $deadline - clock_gettime(CLOCK_MONOTONIC);
    if ($left <= 0) { $failed = 1; last; }
    for my $fh ($select->can_read($left < 0.05 ? $left : 0.05)) {
        my $bytes = '';
        my $n = sysread($fh, $bytes, 16384);
        if (!defined $n) {
            next if $! == EINTR || $! == EAGAIN;
            $failed = 1; last;
        }
        if (fileno($fh) == fileno($ready_r)) {
            if ($n != 1 || $bytes ne '1') { $failed = 1; last; }
            $owned_group = 1;
            # A signal before this acknowledgement still cannot start a command.
            if (!$stop && syswrite($ack_w, '1') != 1) { $failed = 1; }
            close $ack_w;
            $select->remove($ready_r);
        } elsif (!$n) {
            $eof = 1; $select->remove($out_r);
        } else {
            $output .= $bytes;
            # ssh -G is a small config report; refuse an unbounded wrapper stream.
            if (length($output) > 1024 * 1024) { $failed = 1; last; }
        }
    }
}
close $ack_w if defined fileno($ack_w);
# On every outcome, terminate any wrapper descendants, including ones that
# closed stdout. The child remains unreaped, reserving our signal target.
my $target = $owned_group ? -$pid : $pid;
kill 'TERM', $target;
my $grace = clock_gettime(CLOCK_MONOTONIC) + 0.2;
while (clock_gettime(CLOCK_MONOTONIC) < $grace) { sleep 0.01; }
kill 'KILL', $target;
my ($reaped, $status) = (0, 0);
my $reap_deadline = clock_gettime(CLOCK_MONOTONIC) + 1;
while (clock_gettime(CLOCK_MONOTONIC) < $reap_deadline) {
    my $got = waitpid($pid, WNOHANG);
    if ($got == $pid) { $reaped = 1; $status = $?; last; }
    if ($got < 0 && $! != EINTR) { last; }
    sleep 0.01;
}
# No more signals after reaping: the PID/PGID may now be reused. Only observe
# closure, and refuse if an owned group has not disappeared within this bound.
my $absent = !$owned_group;
my $drain_deadline = clock_gettime(CLOCK_MONOTONIC) + 0.5;
while ($owned_group && clock_gettime(CLOCK_MONOTONIC) < $drain_deadline) {
    if (!kill(0, -$pid) && $! == ESRCH) { $absent = 1; last; }
    sleep 0.01;
}
close $out_r; close $ready_r;
exit(128 + $stop) if $stop;
exit 2 unless !$failed && $done && $eof && $reaped && $absent && $status == 0;
print $output or exit 2;
exit(128 + $stop) if $stop;
exit 0;
