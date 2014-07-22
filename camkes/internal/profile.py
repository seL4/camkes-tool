#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

'''
Runtime profiling functionality. Nothing in here is CAmkES-specific. Users
should only interact with this module through the get_profiler function.
'''

import cProfile, inspect, os, pstats, signal, threading, time

class Profiler(object):
    '''Base profiler class. All profilers should inherit from this and
    implement the enable and disable functions. By doing this, all profilers
    should be usable in one of two ways. Firstly by explicitly calling enable
    and disable:

        my_profiler.enable('enclosed operation')
        ...
        my_profiler.disable()

    Secondly by implicitly calling these with a with statement:

        with my_profiler('enclosed operation'):
            ...

    The intention is for users to use the second form when profiling easily
    contained functionality. The first form is provided for flexibility when
    profiling needs to be enabled and then disabled from different function
    contexts.'''
    def __init__(self, output_stream):
        self.out = output_stream

    def enable(self, event=None):
        raise NotImplementedError

    def disable(self):
        raise NotImplementedError

    def __call__(self, event=None):
        self.enable(event)
        return self

    def __enter__(self):
        pass

    def __exit__(self, type, value, traceback):
        self.disable()

class NullProfiler(Profiler):
    '''Profiler that does nothing. For effectively turning profile operations
    into no-ops.'''
    def enable(self, event=None):
        pass

    def disable(self):
        pass

class InternalProfiler(Profiler):
    '''Profiler to provide just basic timing information.'''
    def __init__(self, output_stream):
        super(InternalProfiler, self).__init__(output_stream)
        self.current = []
        self.timestamp = []
        print >>self.out, 'Operation: duration (secs)\n'

    def enable(self, event=None):
        self.current.append(event)
        self.timestamp.append(time.clock())

    def disable(self):
        stop = time.clock()
        assert len(self.current) > 0
        event = self.current.pop()
        assert len(self.timestamp) > 0
        start = self.timestamp.pop()
        print >>self.out, '%(event)s: %(time).2f' % {
            'event':event or '<UNNAMED>',
            'time':stop - start,
        }

class AggregateProfiler(Profiler):
    '''Profiler to give statistical timing for the entire execution.'''
    def __init__(self, output_stream):
        super(AggregateProfiler, self).__init__(output_stream)
        self.pr = cProfile.Profile()
        self.pr.enable()

    def enable(self, event=None):
        pass

    def disable(self):
        pass

    def __del__(self):
        self.pr.disable()
        ps = pstats.Stats(self.pr, stream=self.out).sort_stats('cumulative')
        ps.print_stats()

def ping():
    '''Keep sending SIGUSR1 to ourself. See Heartbeat for the purpose of this.'''
    while True:
        time.sleep(0.5)
        os.kill(os.getpid(), signal.SIGUSR1)

class Heartbeat(Profiler):
    '''Instrumentation that just indicates we're still alive and where we are.'''
    def __init__(self, output_stream):
        super(Heartbeat, self).__init__(output_stream)
        signal.signal(signal.SIGUSR1, self.pulse)
        self.pinger = threading.Thread(target=ping)
        self.pinger.daemon = True
        self.pinger.start()
    def enable(self, event=None):
        pass
    def disable(self):
        pass
    def pulse(self, sig, frame):
        lines = inspect.getsourcelines(frame)[0]
        lineno = frame.f_lineno
        firstlineno = frame.f_code.co_firstlineno
        filename = frame.f_code.co_filename
        print >>self.out, \
            ('%(filename)s:%(lineno)d: %(line)s' % {
            'filename':filename,
            'lineno':lineno,
            'line':lines[lineno - firstlineno],
        }).strip()

class NativeProfiler(Profiler):
    '''Profiler to give statistical timing per operation.'''
    def __init__(self, output_stream):
        super(NativeProfiler, self).__init__(output_stream)
        self.pr = []

    def enable(self, event=None):
        pr = cProfile.Profile()
        self.pr.append((event, pr))
        pr.enable()

    def disable(self):
        assert len(self.pr) > 0
        event, pr = self.pr.pop()
        pr.disable()
        print >>self.out, '%s:\n' % (event or '<UNNAMED>')
        ps = pstats.Stats(pr, stream=self.out).sort_stats('cumulative')
        ps.print_stats()

def get_profiler(type, output_stream):
    profmap = {
        'none':NullProfiler,
        'native':NativeProfiler,
        'aggregate':AggregateProfiler,
        'internal':InternalProfiler,
        'heartbeat':Heartbeat,
    }
    if type not in profmap:
        raise Exception('Unknown profiler %s requested' % type);
    return profmap[type](output_stream)
