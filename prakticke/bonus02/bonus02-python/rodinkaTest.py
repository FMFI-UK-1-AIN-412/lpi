#! /usr/bin/env python3

import sys
import time
import traceback
from Rodinka import Rodinka

Dorothy = 'Dorothy'
Virginia = 'Virginia'
George = 'George'
Howard = 'Howard'
Who = [Dorothy, Virginia, George, Howard]
Masculine = frozenset((George, Howard));
Feminine = frozenset((Dorothy, Virginia));

def now():
    try:
       return time.perf_counter() # >=3.3
    except AttributeError:
       return time.time() # this is not monotonic!

def printException():
    print('ERROR: Exception raised:\n%s\n%s\n%s' % (
        '-'*20,
        traceback.format_exc(),
        '-'*20)
    )

class Tester(object):
    def __init__(self):
        self.case = 0
        self.tested = 0
        self.passed = 0
        self.time = 0

    def fail(self, msg):
        self.tested += 1
        print('  ✕ Failed: %s' % msg)
        return False;

    def verify(self, cond, msg):
        self.tested += 1
        if cond:
            self.passed += 1
            return True
        else:
            print('  ✕ Failed: %s' % msg)
            return False

    def test(self):
        try:
            start = now()
            r = Rodinka().vyries()
            duration = now() - start
            self.time += duration
            print('  Riešenie: otec: %s  matka: %s  syn: %s  dcéra: %s' % (r.otec, r.matka, r.syn, r.dcera));

            passed = [
                self.verify(r.otec in Masculine, r.otec + " nemôže byt otec"),
                self.verify(r.syn in Masculine, r.syn + " nemôže byt syn"),
                self.verify(r.matka in Feminine, r.matka + " nemôže byt matka"),
                self.verify(r.dcera in Feminine, r.dcera + " nemôže byt dcéra")
            ]
            everybody = frozenset((r.otec, r.matka, r.dcera, r.syn));
            for who in Who:
                passed.append(self.verify(who in everybody, who + " chýba"));

            if not all(passed):
                return

            Ts = [
                "George a Dorothy sú pokrvní príbuzní",
                "Howard je starší než George",
                "Virginia je mladšia než Howard",
                "Virginia je staršia než Dorothy",
            ]
            vals = [[False, False, True, False], [True, False, False, True], [True, True, True, False], [True, True, True, True]]
            c = (0 if r.otec == George else  2) + (0 if r.matka == Dorothy else 1);
            ts = 0
            print()
            for ok, t in  zip(vals[c], Ts):
                print('  %s %s' % ('✓' if ok else '✕', t))
                if ok: ts += 1;
            print()

            self.verify(ts == 2, "práve dve tvrdenia sú pravdivé")

        except KeyboardInterrupt:
            pass
        except:
            printException()

    def status(self):
        print('')
        print('TESTED %d' % (self.tested,))
        print('PASSED %d' % (self.passed,))
        print("TIME %1.3fms" % (self.time * 1000.0))
        if self.tested == self.passed:
            print("OK")
            return True
        else:
            print("ERROR")
            return False

t = Tester()
t.test()
sys.exit(0 if t.status() else 1)
