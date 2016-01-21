#> !P3!

#> 1v0 - initial version

# TODO: Our own, well controlled, log roll.

###
### nl2xlog
###
### Watch an nginx log folder to track, convert and 
### transmit access & error logs to a remote XLOG server.
###
### Nginx's log file naming for access.* and error.* files:
###   *.log are the current (dynamic) files.
###   *.1 are the rolled *.log files (semi-static).
###   *.#.gz are the rolled *.1 files (static).
###
### Files progress through folders:
###
###     WATCHPATH: Where current .log (dynamic), 
###                                .1 (semistatic), and 
###                                .gz (static) files 
###                are watched for.
###
###     WORKPATH: Files detected in WATCHPATH are 
###               moved to WORKPATH for actuall processing.
###
###     SENTPATH: Once fully processed in WORKPATH, files
###               are moved here.
###
### To track this program's processing of *.log files, extra
### *.logx files are written, containing sent and crc values 
### that track *.log files processing. These .logx files are 
### rolled to *.1 versions along with the *.log files. The sent 
### and crc info allows the *.1 processing (in WORKPATH) to know
### how much of the originating *.log files has already been
### processed.
###
### ***
### For robustness, a semaphore file should be created and 
### deleted, bracketing nginx's log file rolls, to block 
### this program from processing during a roll.
### ??? Permission to write the semaphore?
###   /etc/logrotate.conf has a 'su root syslog' line.
### ***
###

"""
Usage:
  nl2xlog.py [--ini=<ini> --srcid=<srcid> --subid=<subid> \
  --wpath=<wpath> --donesd=<donesd> --interval=<interval> \
  --dotdiv=<dotdiv>  --txtlen=<txtlen> --ofile=<ofile> \
  --txrate=<txrate>]
  nl2xlog.py (-h | --help)
  nl2xlog.py --version

Options:
  -h --help              Show help.
  --version              Show version.
  --ini=<ini>            Overrides default ini pfn.
  --srcid=<srcid>        Source ID ("nx01" for nginx).
  --subid=<subid>        Sub    ID ("____" for nginx).
  --wpath=<wpath>        Path to watched "access.log" and "error.log".
  --donesd=<donesd>      Subdir of wpath for done files. Null disables.
  --interval=<interval>  Logfile watch interval (seconds).
  --dotdiv=<dotdiv>      Nonzero -> dots to screen, with this divisor.
  --txtlen=<txtlen>      Nonzero -> text to screen, with this maxlen.
  --ofile=<ofile>        TCP/IP address (usually) or a file path (dev/test).
  --txrate=<txrate>      Nonzero -> max transmissions per sec.
"""

import os, sys, stat
import time, datetime, calendar
import shutil
import collections
import pickle
import copy
import json
import configparser
import threading
import re
import gzip
import pytz
import argparse
_ns = argparse.Namespace
import itertools
import binascii
import signal

gP2 = (sys.version_info[0] == 2)
gP3 = (sys.version_info[0] == 3)
assert gP3, 'requires Python 3'

gWIN = sys.platform.startswith('win')
gLIN = sys.platform.startswith('lin')
assert (gLIN or gWIN), 'requires either Linux or Windows'

import pythonpath
pythonpath.set()

import l_dummy
import l_dt as _dt             
import l_misc as _m
import f_helpers as _h

import l_screen_writer
_sw = l_screen_writer.ScreenWriter()             

import l_simple_logger 
_sl = l_simple_logger.SimpleLogger(screen_writer=_sw, log_file_queue=True)###, log_file=LF)

import l_args as _a 

gRPFN = gRFILE = None
EOL = '\n'

####################################################################################################

SRCID = None                # Client source ID. Immutable, from INI.
SUBID = None                # Client subid. Set by message.
WATCHPATH = None            # Watched path. All but .log files are moved to WORKPATH.
WORKPATH = None             # Unchanging files to be sent.
SENTPATH = None             # After sending.
YLOGPATH = None             # Where YLOGGER output and trace data files are written. 
INTERVAL = 6                # Seconds between watcher looks.
DOTDIV = None               # Nonzero -> dots to screen, with this divisor.
TXTLEN = 76###None          # Nonzero -> text to screen, with this maxlen. Default 76.
TXTLEN = None
OXLOG = None                # Socket connection to an xlog server.
OFILE = None                # Flatfile connection (dev/test).
XFILE = None                # Parameter string -> either OXLOG or OFILE.
NLCODING = 'utf-8'          # Just a guess, for now, that nginx uses UTF-8 for its logs.
ENCODING = 'utf-8'          # Start a utf-8 chain, whether to file or xlog.
ERRORS = 'strict'
OXLOGTS = 0                 # Time of last Tx to xlog.
TXRATE = 0                  # Max number of transmissions per sec.
                            # Transformed to 1 / TXRATE after INI read.
AEL, ASL = '0', '?'         # !MAGIC!  ACCESS EL and SL (error and sub levels).
EEL, ESL = '0', '?'         # !MAGIC!  ERROR  ... 
                            # *EL = 0: unset
                            # *SL = 'a'/'e' for access/error logs.
SELF_SRCID = '0002'         # Self logging source ID.  Defined here, immutable.
SELF_SUBID = '____'         # Self logging subid. Set by message.

AELOGTYPES = ('access', 'error')

# Do our own log rolling?
DO_LOGROLL = None                   # Setting ROLLPERIOD sets this.

# The filnames (in WATHPATH) that are to be rolled to .1 versions.
ROLL_FNS = ['access.log', 'access.logx', 'error.log', 'error.logx']

# ROLLSTATE is a dict that's read at program startup and reread 
# following its write/update after a roll.
ROLLSTATE = {'files': ROLL_FNS,     # List of files to roll. 
             'last_lu': None,       # Last roll as local unix timestamp.
             'last_iso': None,      #   ...as iso string.
             'rolled_lu': None,     # Actual last roll timestamp.
             'rolled_iso': None,    #  
             'next_lu': None,       # Next roll timestamp.
             'next_iso': None}      # 
ROLLSTATE_DEFAULT = copy.copy(ROLLSTATE)

# ROLLSTATE dict is json'd here.
ROLLSTATE_FN = 'RollState'  # Stored in WATCHPATH.
# To manually force a roll, create this file in WATCHPATH.
FORCEROLL_FN = 'ForceRoll'

NEXTROLL = None             # yy-mm-dd~hh-mm 
                            # To force a roll, or to initialize 
                            # when no ROLLSTATE file exists.
                            # 24hr local time (minute).
                            # 10 digits, with any, or no, separators.

ROLLPERIOD = None           # String, digit(s) + alpha suffix.
RPM = None                  # Roll period in minutes, derived from 
                            # ROLLPERIOD.  
                            # Suffixes: m)inutes
                            #           h)ours
                            #           d)ays
                            #           w)eeks

NGINX_PID_PATH = '/var/run/nginx.pid'

####################################################################################################

TEST = False                # Hunting short-logrec bug.
TESTONLY = False            # Hunting short-logrec bug.
ONECHECK = False		    # Once around watcher_thread loop.
TIMINGS = False             # Timing in watcher_thread loop.
TRACINGS = False            # Extra details

HEARTBEAT = False###True            # Emit ae='h' heartbeat records (OFILE and OXLOG).
WAIT4OXLOG = True           # Wait for OXLOG to empty.

# Extra debugging? (To simple logger, for now.)
DEBUG = False
YLOG_GZ = True
# Controls which filenames are watched.
DO_ACCESS = True            # access.*
DO_ERROR  = True            # error.*
DO_GZ     = True            # *.gz
DO_N      = True            # #.1..n
DO_LOG    = True            # #.log
DO_MON    = True            # Mode is monitor.

def justDigits(s):
    return ''.join((c for c in s if c.isdigit()))

def doFilename(ft, fn, x=False):

    def isLog():
        nonlocal fn, x
        if fn.endswith('.log') or \
           fn.endswith('.logx') and x:
            return True

    def is1():
        nonlocal fn
        return (fn[-1] == '1')

    def isGz():
        nonlocal fn
        return fn.endswith('.gz')

    if not ( (DO_ACCESS and fn.find('access.log') in (0, 7)) or 
             (DO_ERROR  and fn.find('error.log' ) in (0, 7)) ):
        return False
    return ( (DO_LOG and ft == 0 and isLog()       ) or
             (DO_N   and ft == 1 and is1()         ) or 
             (DO_GZ  and ft == 2 and isGz()        ) or
             (           ft == 3 and '.log.' in fn ) )
    '''...
    return ( (DO_LOG and ft == 0 and fn.endswith('.log')) or
             (DO_N   and ft == 1 and fn[-1].isdigit()   ) or 
             (DO_GZ  and ft == 2 and fn.endswith('.gz') ) or
             (           ft == 3 and '.log.' in fn      ) )
    ...'''

####################################################################################################

SQUAWKED = False            # To stop exception message cascades.
def DOSQUAWK(errmsg, beep=3):
    """For exception blocks."""
    global SQUAWKED
    if not SQUAWKED:
        _m.beep(beep)
        for em in errmsg.split('\n'):
            _yl.error(None, em)
        SQUAWKED = True

####################################################################################################

class YLOGGER():

    def __init__(self, _sl, ylogpath=None):
        self._sl = _sl
        self.ylogpath = ylogpath
        self.ylf = None
        self.ylfbf = []
        self.ydf_sfx = {'a': None, 'e': None}
        self.ydf = {'a': None, 'e': None}
        self.ydfbf = {'a': [], 'e': []}

    def _log(self, s=''):                       # Called by library routines, so no ae.
        1/1
        self._ylog(None, s)
        self._sl._log(s)

    def null(self, ae, s='', d=False):          # 0
        self._ylog(ae, '## 0 '+s, d=d)
        self._sl.null(s)

    def debug(self, ae, s='', d=False):         # 1
        self._ylog(ae, '## 1 '+s, d=d)
        self._sl.debug(s)

    def info(self, ae, s='', d=False):          # 2
        self._ylog(ae, '## 2 '+s, d=d)
        self._sl.info(s)

    def warning(self, ae, s='', d=False):       # 3
        self._ylog(ae, '## 3 '+s, d=d)
        self._sl.warning(s)

    def error(self, ae, s='', d=False):         # 4
        self._ylog(ae, '## 4 '+s, d=d)
        self._sl.error(s)

    def critical(self, ae, s='', d=False):      # 5
        self._ylog(ae, '## 5 '+s, d=d)
        self._sl.critical(s)

    def extra(self, ae, s='', d=False):         # x
        self._ylog(ae, '## x '+s, d=d)
        self._sl.extra(s)

    def ylogopen(self):
        self.ylf = open(os.path.join(self.ylogpath, ME+'.log'), 'a', encoding=ENCODING, errors=ERRORS)
        self._ylog(None)

    def _ylog(self, ae, s='', d=False):
        if not self.ylf:
            if s is not None:
                self.ylfbf.append(s)
        else:
            if self.ylfbf:
                1/1
                for z in self.ylfbf:
                    1/1
                    if z is not None:
                        self.ylf.write(z + EOL)
                self.ylfbf = []
            else:
                if s is not None:
                    self.ylf.write(s + EOL)
        if d and ae:
            self._ydata(ae, s)

    def ylogclose(self):
        try:    self.ylf.close()
        except: pass

    def ydataopen(self, ae, ydf_sfx):
        if self.ydf_sfx[ae] != ydf_sfx:
            self.ydataclose(ae)
        if self.ydf[ae]:
            return
        z = _dt.ut2iso(_dt.locut(), '~').replace(':', '-') + ydf_sfx
        self.ydf[ae] = open(os.path.join(self.ylogpath, z), 'a', encoding=ENCODING, errors=ERRORS)
        self.ydf_sfx[ae] = ydf_sfx
        self._ydata(ae, None)

    def _ydata(self, ae, d):
        if not self.ydf[ae]:
            if d is not None:
                self.ydfbf[ae].append(d)
        else:
            if self.ydfbf[ae]:
                1/1
                for z in self.ydfbf[ae]:
                    1/1
                    if z is not None:
                        self.ydf[ae].write(z + EOL)
                self.ydfbf[ae] = []
            else:
                if d is not None:
                    self.ydf[ae].write(d + EOL)

    def ydataclose(self, ae=None):
        if ae:  aes = (ae, )
        else:   aes = ('a', 'e')
        for z in aes:
            try:    self.ydf[z].close()
            except: pass
        self.ydf_sfx[ae] = self.ydf[ae] = None

    def _log_file(self, lf):
        self._sl._log_file(lf)

    def _flush(self):
        try:    
            self.ylf.flush()
            os.fsync(self.ylf.fileno())
        except: 
            pass
        for ae in ('a', 'e'):
            try:    
                self.ydf[ae].flush()
                os.fsync(self.ydf[ae].fileno())
            except: 
                pass

####################################################################################################

def isFORCEROLL():
    """Force a roll (with a flag file)?"""
    1/1
    p = os.path.join(WATCHPATH, FORCEROLL_FN)
    if os.path.isfile(p):
        1/1
        os.remove(p)
        return True

def getROLLSTATE():
    global ROLLSTATE
    if not DO_LOGROLL:
        return
    try:
        with open(os.path.join(WATCHPATH, ROLLSTATE_FN), 'r') as f:
            ROLLSTATE = json.load(f)
    except:
        ROLLSTATE = copy.copy(ROLLSTATE_DEFAULT)
    return ROLLSTATE

def putROLLSTATE():
    global ROLLSTATE
    if not DO_LOGROLL:
        return
    with open(os.path.join(WATCHPATH, ROLLSTATE_FN), 'w') as f:
        json.dump(ROLLSTATE, f, sort_keys=True)

def initRoller():
    global ROLLPERIOD, RPM, ROLLSTATE, NEXTROLL
    if not DO_LOGROLL:
        return
    me = 'initRoller'.format(ROLLPERIOD), ''
    try:
        lu = _dt.locut()
        liso = _dt.ut2iso(lu, sep='~')
        # Read ROLLSTATE file. 
        getROLLSTATE()
        RPM = ROLLSTATE.get('rpm', None)
        # If ROLLPERIOD has been supplied, it overrides.
        # RPM looks funny, then ROLLPERIOD must be supplied.
        if ROLLPERIOD or RPM is None or RPM < 5:
            # Turn ROLLPERIOD into RPM.
            n, sfx = int(justDigits(ROLLPERIOD[:-1])), ROLLPERIOD[-1].upper()
            if   sfx == 'M':  m = 1
            elif sfx == 'H':  m = 60
            elif sfx == 'D':  m = 24 * 60
            elif sfx == 'W':  m = 7 * 24 * 60
            RPM = m * n
            if RPM < 5:
                errmsg = 'RPM < 5 min: {}'.format(RPM)
                raise ValueError(errmsg)
            ROLLSTATE['rpm'] = RPM
        # A NEXTROLL time given?  Or not last timestamp in ROLLSTATE?
        if NEXTROLL or not ROLLSTATE['last_lu']:
            z = justDigits(NEXTROLL)
            if len(z) != 10:
                errmsg = 'expecting 10 chars but got: {}'.format(z)
                raise ValueError(errmsg)
            nrdt = datetime.datetime.strptime(z, '%y%m%d%H%M')  
            nrlu = _dt.utc2loc(time.mktime(nrdt.timetuple()))   # first roll time local unix
            nriso = _dt.ut2iso(nrlu, '~')
            lrlu = nrlu - RPM * 60                              # last  roll time local unix
            lriso = _dt.ut2iso(lrlu, '~')
            ROLLSTATE['last_lu'] = lrlu
            ROLLSTATE['last_iso'] = lriso
        # Determine next roll timestamp, ensuring that it's in the future.
        lrlu = ROLLSTATE['last_lu']
        lriso = _dt.ut2iso(lrlu, '~')
        assert RPM > 0, 'bad RPM: {}'.format(RPM)
        nrlu = lrlu + RPM * 60
        while nrlu < lu:
            nrlu += RPM * 60
        nriso = _dt.ut2iso(nrlu, '~')
        ROLLSTATE['next_lu'] = nrlu
        ROLLSTATE['next_iso'] = nriso
        msg = 'next log roll @ {}'.format(nriso)
        _sl.info(msg)
        # Update ROLLSTATE file.
        putROLLSTATE()

    except Exception as E:
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise
    finally:
        1/1

####################################################################################################

# Trim whitespace.  Remove trailing comma.  Remove quotes.  '-', ' ', '' -> None.
def _S(s):
    if s is None:
        return
    s = s.strip()
    if s == '':
        return
    s = s.rstrip(',').replace('"', '')
    if s in ['-', ' ', '']:
        s = None
    return s

_LOCTZ = pytz.timezone('America/Vancouver')

# Common Log Format local time str to utc unix-time.
# Depends on whether access or error log.
def CLFlocstr2utcut(ae, locstr):
    # CLF local time to utc.
    # ae==a: [03/Apr/2015:16:56:14 -0700]
    # ae==e: 2015/07/05 23:02:54
    if ae == 'a':
        locstr = locstr[1:-1]
        locdt = datetime.datetime.strptime(locstr, '%d/%b/%Y:%H:%M:%S %z')
        utcdt = locdt.astimezone(pytz.utc)
        utcut = calendar.timegm(utcdt.timetuple())
        pass
    elif ae == 'e':
        locstr = locstr.strip()
        locnaive = datetime.datetime.strptime(locstr, '%Y/%m/%d %H:%M:%S')
        locdt = _LOCTZ.localize(locnaive, is_dst=None)
        utcdt = locdt.astimezone(pytz.utc)
        utcut = calendar.timegm(utcdt.timetuple())
        pass
    else:
        return
    #$#z = _dt.ut2iso(utcut)#$#
    #$#z = z#$#
    return utcut

def tsBDstr(ts):
    # Format timestamp with blank decimal digits.  Decimal point is retained to aid downstream pattern matching.
    return ('{:15.4f}'.format(ts)).replace('.0000', '.    ')

# Pad IP address to 3 character segments.
def ip15(ip, zeros=True):
    me = 'ip15'
    try:
        if zeros:
            y = [('{:03d}'.format(int(z.strip()))) for z in ip.split('.')]
        else:
            y = [('{:3d}'.format(int(z.strip()))) for z in ip.split('.')]
        x = '.'.join(y)
        if len(x) != 15:
            return ip
        return x
    except Exception as E:
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        raise RuntimeError(errmsg)

####################################################################################################

# Example access and error log data:

''' ACCESS...
50.138.70.144 - - [05/Jul/2015:07:24:19 -0700] "GET /static/pix/0005/0021-tn.jpg HTTP/1.1" 200 11730 "http://worldofmen.yuku.com/topic/9735/American-Eros-by-Mark-Henderson" "Mozilla/5.0 (Windows NT 6.1; Trident/7.0; rv:11.0) like Gecko"
104.197.107.164 - - [05/Jul/2015:08:03:38 -0700] "GET / HTTP/1.0" 200 144 "-" "NerdyBot"
184.69.80.202 - - [05/Jul/2015:08:47:15 -0700] "GET /dcm/charts_main HTTP/1.1" 200 2969 "http://184.69.80.202/dcm/charts_main" "Mozilla/5.0 (Windows NT 5.1) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/43.0.2357.130 Safari/537.36"
104.197.105.249 - - [05/Jul/2015:09:45:06 -0700] "GET / HTTP/1.0" 200 160 "-" "NerdyBot"
184.69.80.202 - - [05/Jul/2015:09:58:51 -0700] "GET /dcm/charts_main HTTP/1.1" 200 2969 "http://184.69.80.202/dcm/charts_main" "Mozilla/5.0 (Windows NT 5.1) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/43.0.2357.130 Safari/537.36"
184.69.80.202 - - [05/Jul/2015:10:22:46 -0700] "GET /dcm/charts_main HTTP/1.1" 200 2969 "http://184.69.80.202/dcm/charts_main" "Mozilla/5.0 (Windows NT 5.1) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/43.0.2357.130 Safari/537.36"
37.115.191.104 - - [05/Jul/2015:10:44:47 -0700] "GET / HTTP/1.1" 200 154 "http://modabutik.ru/" "Mozilla/4.0 (compatible; MSIE 6.0; Windows NT 5.1; .NET CLR 1.1.4322; Alexa Toolbar; (R1 1.5))"
37.115.191.104 - - [05/Jul/2015:10:44:48 -0700] "GET / HTTP/1.1" 200 154 "http://modabutik.ru/" "Mozilla/4.0 (compatible; MSIE 6.0; Windows NT 5.1; .NET CLR 1.1.4322; Alexa Toolbar; (R1 1.5))"
37.115.191.104 - - [05/Jul/2015:10:44:49 -0700] "GET / HTTP/1.1" 200 154 "http://modabutik.ru/" "Mozilla/4.0 (compatible; MSIE 6.0; Windows NT 5.1; .NET CLR 1.1.4322; Alexa Toolbar; (R1 1.5))"
...'''

''' ERROR...
2015/07/05 23:02:54 [error] 24153#0: *10758 open() "/var/www/184.69.80.202/testproxy.php" failed (2: No such file or directory), client: 185.49.15.23, server: 184.69.80.202, request: "GET http://testp1.piwo.pila.pl/testproxy.php HTTP/1.1", host: "testp1.piwo.pila.pl"
2015/07/06 04:40:59 [error] 24153#0: *10795 open() "/var/www/micromegadesigns/default.php" failed (2: No such file or directory), client: 87.255.31.98, server: micromegadesigns.com, request: "POST /default.php HTTP/1.1", host: "micromegadesigns.com", referrer: "http://micromegadesigns.com/default.php"
2015/07/06 09:35:34 [error] 24153#0: *10860 "/var/www/184.69.80.202/wp-login/index.html" is not found (2: No such file or directory), client: 126.5.87.16, server: 184.69.80.202, request: "GET /wp-login/ HTTP/1.1", host: "www.m14s.com"
2015/07/12 13:29:00 [error] 1203#0: *458 "/var/www/184.69.80.202/wp-login/index.html" is not found (2: No such file or directory), client: 178.165.56.247, server: 184.69.80.202, request: "GET /wp-login/ HTTP/1.1", host: "www.m14s.com"
2015/07/13 01:57:48 [error] 1203#0: *485 connect() failed (111: Connection refused) while connecting to upstream, client: 104.167.184.100, server: 184.69.80.202, request: "GET /pix/t/Banners%202012%20Solos HTTP/1.1", upstream: "http://192.168.100.6:8080/pix/t/Banners%202012%20Solos", host: "184.69.80.202", referrer: "http://worldofmen.yuku.com/topic/9731/Solos-banners-from-2012"
2015/07/13 01:58:54 [error] 1203#0: *487 connect() failed (111: Connection refused) while connecting to upstream, client: 104.167.184.100, server: 184.69.80.202, request: "GET /pix/t/Banners%202013%20Solos HTTP/1.1", upstream: "http://192.168.100.6:8080/pix/t/Banners%202013%20Solos", host: "184.69.80.202", referrer: "http://worldofmen.yuku.com/topic/9732/Solos-banners-from-2013"
2015/07/11 08:51:09 [error] 1203#0: *137 connect() failed (111: Connection refused) while connecting to upstream, client: 50.128.166.78, server: 184.69.80.202, request: "GET /pix/t/American%20Eros%20by%20Mark%20Henderson HTTP/1.1", upstream: "http://192.168.100.6:8080/pix/t/American%20Eros%20by%20Mark%20Henderson", host: "184.69.80.202", referrer: "http://worldofmen.yuku.com/topic/9735/American-Eros-by-Mark-Henderson"
2015/07/11 05:41:17 [error] 1204#0: *117 connect() failed (111: Connection refused) while connecting to upstream, client: 50.153.128.8, server: 184.69.80.202, request: "GET /pix/t/Banners%202014%20Solos HTTP/1.1", upstream: "http://192.168.100.6:8080/pix/t/Banners%202014%20Solos", host: "184.69.80.202", referrer: "http://worldofmen.yuku.com/topic/9733/Solos-banners-from-2014"
...'''

# Detect a host:port string (IPv4).
def detectHP(s):
    h = p = None
    try:    a, b = s.split(':')
    except: return h, p
    if not b.isdigit():
        return h, p
    for x, c in enumerate(a.split('.')):
        if not c.isdigit():
            return h, p
    if not x == 3:
        return h, p
    h, p = a, int(b)
    return h, p

#
# Example ACCESS and ERROR log records.
#

# '184.69.80.202|-|-|[07/Dec/2015:15:04:31|-0800]|"GET /dcm/dcTnPD/T1/0/4/15/-.-? HTTP/1.1"|200|1504|"http://184.69.80.202/dcm/dcTnPD/T1/1/4/15/-.-"|"Mozilla/5.0 (Windows NT 5.1) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/46.0.2490.86 Safari/537.36"'

A0 = '108.212.110.142 - - [03/Aug/2015:12:53:06 -0700] "GET /pix/t/American%20Eros%20by%20Mark%20Henderson HTTP/1.1" 200 46 "http://worldofmen.yuku.com/topic/9735/American-Eros-by-Mark-Henderson" "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_9_5) AppleWebKit/600.7.12 (KHTML, like Gecko) Version/7.1.7 Safari/537.85.16"'
A1 = '{"_el": "0", "_id": "TEST", "_ip": null, "_si": "test", "_sl": "_", "_ts": "1438631586.    ", "ae": "a", "body_bytes_sent": 46, "http_referer": "http://worldofmen.yuku.com/topic/9735/American-Eros-by-Mark-Henderson", "http_user_agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_9_5) AppleWebKit/600.7.12 (KHTML, like Gecko) Version/7.1.7 Safari/537.85.16", "remote_addr": "108.212.110.142", "remote_user": null, "request": "GET /pix/t/American%20Eros%20by%20Mark%20Henderson HTTP/1.1", "status": 200, "time_local": "[03/Aug/2015:12:53:06 -0700]", "time_utc": 1438631586}'

A2 = '169.229.3.94 - - [05/Jun/2015:23:16:10 -0700] " " 400 181 "-" "-"'
A3 = '{"_el": "0", "_id": "TEST", "_ip": null, "_si": "test", "_sl": "_", "_ts": "1433571370.    ", "ae": "a", "body_bytes_sent": 181, "http_referer": null, "http_user_agent": null, "remote_addr": "169.229.3.94", "remote_user": null, "request": "_", "status": 400, "time_local": "[05/Jun/2015:23:16:10 -0700]", "time_utc": 1433571370}'

A4 = '184.69.80.202 - - [07/Dec/2015:15:04:31 -0800] "GET /dcm/dcTnPD/T1/0/4/15/-.-? HTTP/1.1" 200 1504 "http://184.69.80.202/dcm/dcTnPD/T1/1/4/15/-.-" "Mozilla/5.0 (Windows NT 5.1) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/46.0.2490.86 Safari/537.36"'
A5 = '{"_el": "0", "_id": "TEST", "_ip": null, "_si": "test", "_sl": "_", "_ts": "1449529471.    ", "ae": "a", "body_bytes_sent": 1504, "http_referer": "http://184.69.80.202/dcm/dcTnPD/T1/1/4/15/-.-", "http_user_agent": "Mozilla/5.0 (Windows NT 5.1) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/46.0.2490.86 Safari/537.36", "remote_addr": "184.69.80.202", "remote_user": null, "request": "GET /dcm/dcTnPD/T1/0/4/15/-.-? HTTP/1.1", "status": 200, "time_local": "[07/Dec/2015:15:04:31 -0800]", "time_utc": 1449529471}'

A6 = '80.69.249.123 - - [11/Dec/2015:14:58:49 -0800] "HEAD / HTTP/1.0" 200 0 "-" "-"'
A7 = '{"_el": "0", "_id": "TEST", "_ip": null, "_si": "test", "_sl": "_", "_ts": "1449874729.    ", "ae": "a", "body_bytes_sent": 0, "http_referer": null, "http_user_agent": null, "remote_addr": "80.69.249.123", "remote_user": null, "request": "HEAD / HTTP/1.0", "status": 200, "time_local": "[11/Dec/2015:14:58:49 -0800]", "time_utc": 1449874729}'

E0 = '2015/08/03 17:48:28 [error] 1199#0: *2502 open() "/var/www/184.69.80.202/wordpress/wp-login.php" failed (2: No such file or directory), client: 58.8.154.9, server: 184.69.80.202, request: "GET /wordpress/wp-login.php HTTP/1.1", host: "wp.go-print.com"'
E1 = '{"_el": "0", "_id": "TEST", "_ip": null, "_si": "test", "_sl": "_", "_ts": "1438649308.    ", "ae": "e", "status": "[error]", "stuff": "1199#0:\\t*2502\\topen()\\t\\"/var/www/184.69.80.202/wordpress/wp-login.php\\"\\tfailed\\t(2:\\tNo\\tsuch\\tfile\\tor\\tdirectory),\\tclient:\\t58.8.154.9,\\tserver:\\t184.69.80.202,\\trequest:\\t\\"GET /wordpress/wp-login.php HTTP/1.1\\",\\thost:\\t\\"wp.go-print.com\\"", "time_local": "2015/08/03 17:48:28", "time_utc": 1438649308}'

E2 = '2015/11/24 07:59:59 [error] 32408#0: *1 open() "/usr/share/nginx/html/pages/j-kelly-dresser.html" failed (2: No such file or directory), client: 184.69.80.202, server: kellydresser.com, request: "GET / HTTP/1.1", host: "kellydresser.com"'
E3 = '{"_el": "0", "_id": "TEST", "_ip": null, "_si": "test", "_sl": "_", "_ts": "1448380799.    ", "ae": "e", "status": "[error]", "stuff": "32408#0:\\t*1\\topen()\\t\\"/usr/share/nginx/html/pages/j-kelly-dresser.html\\"\\tfailed\\t(2:\\tNo\\tsuch\\tfile\\tor\\tdirectory),\\tclient:\\t184.69.80.202,\\tserver:\\tkellydresser.com,\\trequest:\\t\\"GET / HTTP/1.1\\",\\thost:\\t\\"kellydresser.com\\"", "time_local": "2015/11/24 07:59:59", "time_utc": 1448380799}'

E4 = '2015/11/24 07:59:56 [warn] 32401#0: only the last index in "index" directive should be absolute in /etc/nginx/vhosts.cfg:113'
E5 = '{"_el": "0", "_id": "TEST", "_ip": null, "_si": "test", "_sl": "_", "_ts": "1448380796.    ", "ae": "e", "status": "[warn]", "stuff": "32401#0:\\tonly\\tthe\\tlast\\tindex\\tin\\t\\"index\\"\\tdirective\\tshould\\tbe\\tabsolute\\tin\\t/etc/nginx/vhosts.cfg:113", "time_local": "2015/11/24 07:59:56", "time_utc": 1448380796}'

E6 = '2015/07/08 10:18:54 [error] 24152#0: *11229 open() "/var/www/184.69.80.202/ROADS/cgi-bin/search.plHTTP/1.0"" failed (2: No such file or directory), client: 31.184.194.114, server: 184.69.80.202, request: "GET /ROADS/cgi-bin/search.plHTTP/1.0" HTTP/1.1", host: "184.69.80.202"'
#6 = '2015/07/08 10:18:54 [error] 24152#0: *11229 open() "/var/www/184.69.80.202/ROADS/cgi-bin/search.pl" failed (2: No such file or directory), client: 31.184.194.114, server: 184.69.80.202, request: "GET /ROADS/cgi-bin/search.pl HTTP/1.1", host: "184.69.80.202"'
E7 = '{"_el": "0", "_id": "TEST", "_ip": null, "_si": "test", "_sl": "_", "_ts": "1436375934.    ", "ae": "e", "status": "[error]", "stuff": "24152#0:\\t*11229\\topen()\\t\\"/var/www/184.69.80.202/ROADS/cgi-bin/search.pl\\"\\tfailed\\t(2:\\tNo\\tsuch\\tfile\\tor\\tdirectory),\\tclient:\\t31.184.194.114,\\tserver:\\t184.69.80.202,\\trequest:\\t\\"GET /ROADS/cgi-bin/search.pl HTTP/1.1\\",\\thost:\\t\\"184.69.80.202\\"", "time_local": "2015/07/08 10:18:54", "time_utc": 1436375934}'

#
# parseLogrec   
#               
def parseLogrec(ae, logrec):
    """Parse logrec into chunks."""
    me = 'parseLogrec({}, {})'.format(repr(ae), repr(logrec))
    rc, rm, chunks = -1, '???', None
    try:

        # Blanks and quoted blanks.
        z = logrec
        if '  ' in logrec:
            logrec = logrec.replace('  ', ' ')
        logrec = logrec.replace(' " " ', ' "_" ')   # OK to lose a quoted blank.  Shouldn't appear at front or back.
        if logrec != z:
            z, logrec = z, logrec

        # nginx has a quirk: 
        z = logrec
        y = 'HTTP/1.0"'                             # These are inserted randomly and the extra '"' screws up quoting.
        undo_lc = False
        while True:
            x = logrec.find(y)
            if x == -1:
                break
            if logrec[x-1] == ' ':
                logrec = logrec.replace(y, y.lower())   # Hide.
                undo_lc = True
            else:
                logrec = logrec.replace(y, '')          # !!! Zap!
        if undo_lc:
            logrec = logrec.replace(y.lower(), y)
        if logrec != z:
            z, logrec = z, logrec

        # Find blank separated words.
        words = logrec.split(' ')
        chunks = []
        quoted = False

        # Recombine quoted chunks.  Keep quotes.
        for wrd in words:
            if quoted:
                chk += (' ' + wrd)
                if wrd.endswith('"') or wrd.endswith('",'):
                    chunks.append(chk)
                    chk = ''
                    quoted = False
                else:
                    1/1
            else:
                if wrd[0] == '"':
                    if wrd.endswith('"') or wrd.endswith('",'):
                        chk = wrd
                        chunks.append(chk)
                    else:
                        chk = wrd
                        quoted = True
                else:
                    chunks.append(wrd)
        chunks = chunks

        # Check quoted chunks.
        for chk in chunks:
            if chk[0] == '"':
                if not ((chk[-1] == '"') or chk.endswith('",')):
                    _m.beep(1)
                    logrec = logrec
                    chk = chk
                    chunks = chunks
                    errmsg = 'bad chunk: {}: {}'.format(chk, logrec)
                    ###_yl.error(errmsg)
                    rc, rm = 1, errmsg
                    return rc, rm, chunks

        # Done.
        rc, rm, chunks = 0, 'OK', chunks
        return rc, rm, chunks

    except Exception as E:
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise
    finally:
        if rc != 0:
            rc, rm, chunks = rc, rm, chunks
        1/1

#
# genACCESSorec
#
def genACCESSorec(chunks, ae, el, sl, srcid, subid, decorated=False):
    """Generate an ACCESS orec from chunks."""
    me = 'genACCESSorec'
    rc, rm, orec, vrec = -1, '???', None, None
    try:

        if len(chunks) != 10:
            errmsg = 'expecting 10 fields but got {} from: {}'.format(len(chunks), repr('|'.join(chunks)))
            rc, rm = 1, errmsg
            return rc, rm, orec, vrec

        (remote_addr, ignored, remote_user, 
            a, b, request, status, 
            body_bytes_sent, http_referer, http_user_agent) = chunks
        if request in ('', '""', '"_"'):
            request = None
        time_local = a + ' ' + b                    # '[03/Aug/2015:12:53:06' + ' ' + '-0700]'
        if remote_user == '-':
            remote_user = None

        time_utc = CLFlocstr2utcut(ae, time_local)  # 1438631586                # '1438631586.    '
        time_utc_iso = _dt.ut2iso(time_utc)         # '2015-08-03 19:53:06'
        status = int(status)
        body_bytes_sent = int(body_bytes_sent)
        remote_addr     = remote_addr
        ignored         = ignored
        remote_user     = remote_user
        time_local      = time_local
        time_utc        = time_utc
        time_utc_iso    = time_utc_iso
        status          = status
        request         = request
        body_bytes_sent = body_bytes_sent
        http_referer    = http_referer
        http_user_agent = http_user_agent
        logdict = {
            '_ip'             : None,               # Will be filled in by logging server.
            '_ts'             : tsBDstr(time_utc),  # '1234567890.    ' format.
            '_id'             : srcid,
            '_si'             : subid,
            '_el'             : el,                 # Raw, base error_level.
            '_sl'             : sl,                 # Raw, base sub_level.
            'ae'              : ae,                 # Access or Error.
            'remote_addr'     : remote_addr,
            'remote_user'     : remote_user,
            'time_local'      : time_local,
            'time_utc'        : time_utc,
            'status'          : status,
            'request'         : _S(request),
            'body_bytes_sent' : body_bytes_sent,
            'http_referer'    : _S(http_referer), 
            'http_user_agent' : _S(http_user_agent)
        }

        rc, rm = 0, 'OK'        
        ldj = json.dumps(logdict, ensure_ascii=True, sort_keys=True)
        if decorated:
            # Prepend a copy of the timetamp (for sorting).
            orec = '{}|{}|{}'.format(logdict['_ts'], ae, ldj)  
        else:
            orec = ldj

        if TXTLEN and (TXTLEN > 0):
            vrec = ('{}|{}|{}|{}|{}'.format(ip15(remote_addr), str(el), str(sl), ae, str(request)))[:TXTLEN]
            vrec = vrec

        return rc, rm, orec, vrec

    except Exception as E:
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise
    finally:
        1/1

#
# genERRORorec
#
def genERRORorec(chunks, ae, el, sl, srcid, subid, decorated=False):
    """Generate an ERROR orec from chunks."""

    def chunkspop0():
        try:    return chunks.pop(0)
        except: return None

    me = 'genERRORorec'
    rc, rm, orec, vrec = -1, '???', None, None
    try:

        original_chunks = copy.copy(chunks)     # !DEBUG!

        if False and len(chunks) < 3:           # !DEBUG!
            errmsg = 'no chunks!'
            _m.beep(1)
            _yl.error(None, errmsg)
            1/1
            return rc, rm, orec, vrec
        else:
            1/1

        try:
            time_local = chunkspop0() + ' ' + chunkspop0()
            time_utc = CLFlocstr2utcut(ae, time_local)
            time_utc_iso = _dt.ut2iso(time_utc)
        except Exception as E:
            1/1
            errmsg = 'failure reading timestamp'
            rc, rm = 1, errmsg
            1/1
            return rc, rm, orec, vrec

        status = chunkspop0()
        if status not in ('[warn]', '[error]'):  
            errmsg = 'unexpected status: ' + repr(status)
            pass        # POR

        if status == '[warn]':
            pass

        # The remaining chunks are inconsistently formatted "stuff".
        stuff = '\t'.join(chunks)

        # But try to find "remote_addr", "request", "server".
        remote_addr, request, server = '999.999.999.999', '', ''
        z = copy.copy(chunks)
        while z:
            y = z.pop(0)
            if y == 'client:':
                remote_addr = z.pop(0).rstrip(',')
                continue
            if y == 'server:':
                server = z.pop(0).rstrip(',')
                continue
            if y == 'request:':
                request = z.pop(0).rstrip(',')
        remote_addr, request, server = remote_addr, request, server
        if not request:
            chunks = chunks

        # Skeleton ERROR logdict.
        logdict = {
            '_ip'             : None,               # Will be filled in by logging server.
            '_ts'             : tsBDstr(time_utc),  # '1234567890.    ' format.
            '_id'             : srcid,
            '_si'             : subid,
            '_el'             : el,                 # Raw, base error_level.
            '_sl'             : sl,                 # Raw, base sub_level.
            'ae'              : ae,                 # Access or Error.
            'time_local'      : time_local,
            'time_utc'        : time_utc,
            'status'          : status,             # In ('[warn]', '[error]').
            'stuff'           : stuff               # Inconsistently formatted stuff. 
        }

        rc, rm = 0, 'OK'        
        ldj = json.dumps(logdict, ensure_ascii=True, sort_keys=True)
        if decorated:
            # Prepend a copy of the timetamp (for sorting).
            orec = '{}|{}|{}'.format(logdict['_ts'], ae, ldj)  
        else:
            orec = ldj

        if TXTLEN and (TXTLEN > 0):
            vrec = ('{}|{}|{}|{}|{} {}'\
                    .format(ip15(remote_addr), str(el), str(sl), ae, server, request))[:TXTLEN]
            vrec = vrec

        return rc, rm, orec, vrec

    except Exception as E:
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise
    finally:
        if rc != 0:
            rc, rm, orec, vrec = rc, rm, orec, vrec
        1/1

####################################################################################################

#
# shutDown
#
def shutDown():
    try:  OXLOG.disconnect()
    except:  pass
    try:  OFILE.close()
    except:  pass

#
# sendLogrec
#
def sendLogrec(ae, logrec):
    """Send a raw log record: parse, gen a/e orec, output to xlog/file."""
    ###me = 'sendLogrec({}, {})'.format(repr(ae), repr(logrec))
    me = 'sendLogrec'
    try:

        original_logrec = logrec        # !DEBUG!   -> '\x1a'
        if original_logrec == '\x1a':
            _m.beep(1)
            1/1

        # logrec?
        try:    logrec = logrec.strip()
        except: logrec = None
        if not logrec:
            return
            
        # Parse logrec.
        rc, rm, chunks = parseLogrec(ae, logrec)
        if rc != 0:
            _m.beep(1)
            try:    z = '|'.join(chunks)
            except: z = ''
            errmsg = '{}: parse_logrec: {}:, {}, {}'.format(me, rc, rm, z)
            _yl.error(ae, errmsg)
            return

        # ACCESS log?
        if   ae == 'a':
            rc, rm, orec, vrec = genACCESSorec(chunks, 'a', AEL, 'a', SRCID, SUBID)
            if rc != 0:
                _m.beep(1)
                try:    z = '|'.join(chunks)
                except: z = ''
                errmsg = '{}: gen_access_orec: {}:, {}, {}'.format(me, rc, rm, z)
                _yl.error(ae, errmsg)
                return
            
        # ERROR log?
        elif ae == 'e':
            rc, rm, orec, vrec = genERRORorec(chunks, 'e', EEL, 'e', SRCID, SUBID)
            if rc != 0:
                _m.beep(1)
                try:    z = '|'.join(chunks)
                except: z = ''
                errmsg = '{}: parse_gen_error_orec: {}:, {}, {}'.format(me, rc, rm, z)
                _yl.error(ae, errmsg)
                return

        else:
            raise ValueError('export: bad _ae: ' + repr(ae))

        # TCP/IP?
        if OXLOG:
            try:
                rc = OXLOG.send(orec.encode(encoding=ENCODING, errors=ERRORS))
            except Exception as E:
                errmsg = '{}: oxlog: {}'.format(me, E)
                DOSQUAWK(errmsg)
                raise

        # Flatfile?
        if OFILE:
            try:
                OFILE.write(orec + '\n')    # Opened with encoding=ENCODING, errors=ERRORS.
            except Exception as E:
                errmsg = '{}: ofile: {}'.format(me, E)
                DOSQUAWK(errmsg)
                raise

        # Screen?
        if TXTLEN and vrec and (TXTLEN > 0):
            _yl.extra(ae, vrec)
        else:
            _sw.iw('.')

        # YDATA.
        _yl._ydata(ae, orec)

    except Exception as E:
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise
    finally:
        1/1


#
# Send a file (either type 1 or 2) via pfn.
# Will be in WORKPATH.
#
def sendStaticFile(ae, ydf_sfx, src):
    global FWTSTOP
    1/1
    """Send a file (from src pfn)."""
    _, fn = os.path.split(src)
    me = 'sendFile({})'.format(fn)
    try:
        _yl.ydataopen(ae, ydf_sfx)
        _yl.warning(ae, '{} sending {}'.format(_dt.ut2iso(_dt.locut()), fn), d=True)
        if    '-access.log' in src:  ae = 'a' 
        elif  '-error.log'  in src:  ae = 'e' 
        else: raise ValueError('{}: funny filename'.format(me)) 
        1/1
        if src.endswith('.gz'): f = gzip.open(src, 'r')
        else:                   f = open(src, 'r')
        for x, logrec in enumerate(f):
            if FWTSTOP:
                break
            if isinstance(logrec, bytes):
                logrec = logrec.decode(encoding=ENCODING, errors=ERRORS)
            sendLogrec(ae, logrec)
        1/1
        _yl.warning(ae, '{} sent    {}'.format(_dt.ut2iso(_dt.locut()), fn), d=True)    
        _yl._flush()
        return True
    except Exception as E:
        FWSTOP = True
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise
    finally:
        1/1
        # End dots.
        _sw.nl()
        # Close src file.
        try:    f.close
        except: pass
        _yl.ydataclose()
        # Wait for OXLOG to flush?
        if WAIT4OXLOG and OXLOG:
            nsw = 0
            try:
                while len(OXLOG.txbacklog) > 1:
                    _sw.iw('|')
                    time.sleep(1)
                    nsw += 1
                    if nsw > 180:                        # !MAGIC!  Give up after three minutes.
                        raise RuntimeError('OXLOG flush timeout')
                _sw.nl()
            except Exception as E:
                errmsg = '{}: {}'.format(me, E)
                DOSQUAWK(errmsg)
                raise
            pass
        1/1

#
# Incrementally send a dynamic file's new stuff.
#
def incrementDynamicFile(ae, fi, lxd=None):
    """Send new content from a dynamic file."""
    global FWTSTOP
    me = 'incrementDynamicFile({})'.format(fi.filename)
    nbs = 0
    try:

        if lxd:  lxdsent = lxd.sent
        else:    lxdsent = 0
        btr = fi.size - lxdsent

        # Already sent?
        if btr == 0:
            1/1
            ###---_yl.warning(ae, '{} nothing to send from {}'.format(_dt.ut2iso(_dt.locut()), fi.filename), d=True)
            return nbs

        _yl.warning(ae, '{} sending [{:,d} .. {:,d}) from {}'.format(_dt.ut2iso(_dt.locut()), lxdsent, fi.size, fi.filename), d=True)
        if DEBUG:
            _yl.debug('{}  >> export  {}  {}'.format(_dt.ut2iso(_dt.locut()), fi.ae, fi.filename))
            dumpFI(_yl.debug, fi)

        1/1
        # Dynamic files must be text. 
        # Seek from SOF to the start of new data.
        # Read the file to its advertised length.
        # Convert the bytes to str and split by lines.
        pfn = os.path.normpath(location2path(fi.location) + '/' + fi.filename)
        with open(pfn, 'rb') as f:
            if lxdsent > 0:
                1/1
                _yl.warning(ae, 'skipping {:,d} bytes'.format(lxdsent), d=True)
                f.seek(lxd.sent)
                1/1
            _yl.warning(ae, 'reading {:,d} bytes'.format(btr), d=True)
            bs = f.read(btr)
            if lxd:
                lxd.crc = binascii.crc32(bs, lxd.crc)
            for x, logrec in enumerate(bs.decode(encoding=ENCODING, errors=ERRORS).split('\n')):
                1/1
                if FWTSTOP:
                    break
                sendLogrec(fi.ae, logrec)
                1/1
            nbs = len(bs)
            1/1
            # Update logdata with fi values.
            if lxd:
                1/1
                assert (lxdsent + nbs) == fi.size
                1/1
                lxd.modified = fi.modified
                lxd.sent = fi.size          # All was sent.
                lxd.size = fi.size
                1/1
            else:
                1/1
            1/1

        1/1
        _yl.warning(ae, '{} sent    [{:,d} .. {:,d}) from {}'.format(_dt.ut2iso(_dt.locut()), lxdsent, fi.size, fi.filename), d=True)
        1/1
        return nbs

    except KeyboardInterrupt as E:
        FWTSTOP = True
        # sendDynamic:
        _m.beep(1)
        msg = '{}: KI: {}'.format(me, E)
        _yl.warning(ae, msg)
        pass    # Let the thread exit.  Avoids "Exception in thread...".
    except Exception as E:
        FWTSTOP = True
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise
    finally:
        1/1
        # End dots.
        _sw.nl()
        # Wait for OXLOG to flush?
        if WAIT4OXLOG and OXLOG:
            1/1
            nsw = 0
            try:
                while len(OXLOG.txbacklog) > 1:
                    _sw.iw('|')
                    time.sleep(1)
                    nsw += 1
                    if nsw > 180:                        # !MAGIC!  Give up after three minutes.
                        raise RuntimeError('OXLOG flush timeout')
                _sw.nl()
            except Exception as E:
                errmsg = '{}: {}'.format(me, E)
                DOSQUAWK(errmsg)
                raise
            1/1
        1/1

#
# dumpFI
#
def dumpFI(sl, fi, pfx=''):
    me = 'dumpFI'
    try:
        sl('{}  location: {}'.format(pfx, fi.location))
        sl('{}  filename: {}'.format(pfx, fi.filename))
        sl('{}  filetype: {}'.format(pfx, fi.filetype))
        sl('{}        ae: {}'.format(pfx, fi.ae))
        sl('{}  modified: {}'.format(pfx, fi.modified))
        sl('{}      size: {}'.format(pfx, fi.size))
    except Exception as E:
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise
    
#
# What's the filename prefix for the next WORKPATH/SENTPATH log file?
# All such files end with either '.1' or '.gz'.
# Log files will have '.log.' in their names.
# The auxilliary '.logx.' files are not counted, and they don't
# get a prefix.
# !MAGIC! The filename prefix is 6 digits (leading zeros) + '-'.
#
def nextWORKSENTfnpfx():
    maxpfx = None
    for fn in itertools.chain(os.listdir(WORKPATH), os.listdir(SENTPATH)):
        pfx = fn[:6]
        if '.log.' in fn and (not maxpfx or pfx > maxpfx):
            maxpfx = pfx
    if not maxpfx:
        maxpfx = '000000'
    return '{:06d}-'.format(int(maxpfx) + 1)

#
# watcherThread
#
FWTRUNNING = False  # File Watcher Thread Running.
FWTSTOP = False     # To signal a thread stop.
FWTSTOPPED = False  # To acknowledge a thread stop.
def watcherThread():                                                # !WT! 
    """A thread to watch WATCHPATH for files to process."""
    global FWTRUNNING, FWTSTOP, FWTSTOPPED

    #
    # sendHeartbeat
    #
    def sendHeartbeat():
        1/1
        me = 'sendHeartbeat'
        try:

            # Heartbeat?
            if HEARTBEAT:
                1/1
                try:
                    logdict = {
                        '_ip'             : None,               # Will be filled in by logging server.
                        '_ts'             : uuts,               # '1234567890.9876' format.
                        '_id'             : SRCID,
                        '_si'             : SUBID,
                        '_el'             : '0',                # Raw, base error_level.
                        '_sl'             : 'h',                # Heartbeat.
                        'ae'              : 'h',                # Access or Error or Heartbeat.
                        'dt_utc'          : uuiosfs,    
                        'dt_loc'          : uliosfs
                    }
                    orec = json.dumps(logdict, ensure_ascii=True, sort_keys=True) 
                    if OXLOG:
                        try:
                            rc = OXLOG.send(orec.encode(encoding=ENCODING, errors=ERRORS))
                        except Exception as E:
                            errmsg = '{}: heartbeat oxlog: {}'.format(me, E)
                            DOSQUAWK(errmsg)
                            raise
                    if OFILE:
                        try:
                            OFILE.write(orec + '\n')    # Opened with encoding=ENCODING, errors=ERRORS.
                        except Exception as E:
                            errmsg = '{}: heartbeat ofile: {}'.format(me, E)
                            DOSQUAWK(errmsg)
                            raise
                except Exception as E:
                    errmsg = '{}: heartbeat E: {}'.format(me, E)
                    DOSQUAWK(errmsg)
                    raise
                1/1
            1/1

        except Exception as E:
            errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
            DOSQUAWK(errmsg)
            raise

    #
    # fn2ae
    #
    def fn2ae(fn):
        if   'access' in fn:  return 'a'
        elif 'error'  in fn:  return 'e'
        else               :  return '?'

    #
    # checkLogRolling
    # 
    def checkLogRolling():
        """Check for and possibly do nginx log rolling."""
        1/1
        if not DO_LOGROLL:
            return
        me = 'checkLogRolling'
        try:
            forceroll = isFORCEROLL()   # Use below, variously.
            lu = _dt.locut()
            liso = _dt.ut2iso(lu, '~')
            nlu = float(ROLLSTATE['next_lu'])
            nliso = ROLLSTATE['next_iso']
            1/1
            if forceroll or (nlu and (lu > nlu)):
                1/1
                # Roll files.
                nrolled, rolled = 0, []
                # Find .log's and .log.1's.
                fi1s = getFIs(WATCHPATH, 1)
                if fi1s:
                    1/1
                    # Unprocessed .1 files.
                    _m.beep(3)
                    errmsg = '{} old .1 files: {}'.format(len(fi1s), [z.filename for z in fi1s])
                    _sl.error(errmsg)
                    1/1
                else:
                    1/1
                    fi0s = getFIs(WATCHPATH, 0, True)
                    if not fi0s:
                        1/1
                        _m.beep(1)
                        msg = 'no .log files'
                        _sl.warning(msg)
                        1/1
                    else:
                        1/1
                        # Roll logfiles. Empty files are not ignored 
                        # bcs their associated .logx files would 
                        # otherwise be rolled alone.
                        try:
                            for fi0 in fi0s:
                                1/1
                                rolled.append(fi0.filename)
                                src = os.path.join(WATCHPATH, fi0.filename)
                                snk = src + '.1'
                                shutil.move(src, snk)
                                # Recreate .log files.
                                if src[-1] != 'x':
                                    1/1
                                    with open(src, 'w') as f:
                                        pass
                                else:
                                    1/1
                                nrolled += 1
                        except Exception as E:
                            errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
                            DOSQUAWK(errmsg)
                            raise
                        if nrolled:
                            1/1
                            if forceroll:
                                msg = 'forced a roll'
                                _sl.info(msg)
                            msg = '{} rolled: {}'.format(nrolled, rolled)
                            _sl.info(msg)
                            # Signal nginx to repopen its logs.
                            if gLIN:
                                try:
                                    os.kill(int(open(NGINX_PID_PATH).read()), signal.SIGUSR1)
                                    msg = 'signalled nginx to reopen logs'
                                    _sl.info(msg)
                                    time.sleep(INTERVAL / 2)   
                                except Exception as E:
                                    _m.beep(3)
                                    errmsg = 'could not signal nginx: {}'.format(E)
                                    _sl.error(errmsg)
                            1/1
                        1/1
                    1/1
                1/1
                # Always update ROLLSTATE, at least partially.
                ROLLSTATE['rolled_lu'] = lu
                ROLLSTATE['rolled_iso'] = liso
                if not forceroll:
                    ROLLSTATE['last_lu'] = ROLLSTATE['next_lu']
                    ROLLSTATE['last_iso'] = ROLLSTATE['next_iso']
                    ROLLSTATE['next_lu'] = None
                    ROLLSTATE['next_iso'] = None
                else:
                    1/1
                # Save ROLLSTATE.
                putROLLSTATE()
                # Reget ROLLSTATE to get new next_lu/iso values.
                initRoller()
            1/1
        except Exception as E:
            errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
            DOSQUAWK(errmsg)
            raise
        '''...
        blkpfn = os.path.join(WATCHPATH, 'rolling')
        return os.path.isfile(blkpfn)
        ...'''

    #
    # sendWORKPATHgzs
    #
    def sendWORKPATHgzs():
        1/1
        me = 'sendWORKPATHgzs'
        try:

            while True:
                1/1
                kfis2 = getFIs(WORKPATH, 2)
                if not kfis2:
                    break
                1/1
                for fi in kfis2:
                    1/1
                    if FWTSTOP:
                        break
                    ae = fn2ae(fi.filename)
                    src = os.path.join(WORKPATH, fi.filename)
                    if '.logx.' in src:
                        1/1
                        # .gz'd *.logx files are uninteresting.
                        os.remove(src)
                        continue
                    snk = os.path.join(SENTPATH, fi.filename)
                    if sendStaticFile(ae, '-GZ-{}'.format(fi.filename), src):
                        shutil.move(src, snk)
                    else:
                        _m.beep(3)
                        errmsg = 'sendStaticFile({}) failed!'.format(src)
                        raise RuntimeError(errmsg)
                    1/1
                1/1
            1/1

        except Exception as E:
            errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
            DOSQUAWK(errmsg)
            raise

    #
    # sendWORKPATH1s
    #
    def sendWORKPATH1s():
        # There's a delay INTERVAL / 2 before processing files.
        1/1
        me = 'sendWORKPATH1s'
        try:
            while True:
                1/1
                kfis1 = getFIs(WORKPATH, 1)
                if not kfis1:
                    break
                # A additional wait to let nginx's logging settle.
                _sw.wait(INTERVAL / 2)
                1/1
                for fi1 in kfis1:
                    1/1
                    if FWTSTOP:
                        break
                    ae = fn2ae(fi1.filename)
                    src = os.path.join(WORKPATH, fi1.filename)
                    if '.logx.' in src:
                        # Ignore until later.
                        continue
                    _yl.ydataopen(ae, '-1-{}'.format(fi1.filename))
                    _yl.warning(ae, '{} opening {}'.format(_dt.ut2iso(_dt.locut()), fi1.filename), d=True)
                    snk = os.path.join(SENTPATH, fi1.filename)
                    logtype = getLogType(fi1.filename)
                    logxdata = getLogxData(WORKPATH, logtype, sfx='.1')
                    if not logxdata.modified:
                        msg = 'no .logx.1 file for: {}'.format(fi1.filename)
                        _yl.warning(ae, msg, d=True)
                        logxdata.verified = True    # Can't be verified.
                    # Trust logxdata.sent, but verify the crc (and only once).
                    fi1.sent = logxdata.sent
                    if logxdata.sent:
                        if not logxdata.verified:
                            with open(src, 'rb') as f:
                                1/1
                                bs = f.read(logxdata.sent)
                                # ??? Check that bs ends with a \n?
                                fi1.crc = binascii.crc32(bs, 0)
                            if fi1.crc != logxdata.crc:
                                fi1.sent = 0 
                            logxdata.verified = True        # Verify crc only once!
                    else:
                        logxdata.verified = True    # Can't be verified.
                    1/1
                    nbs = incrementDynamicFile(ae, fi1, logxdata)
                    putLogxData(logxdata, WORKPATH, logtype, sfx='.1')
                    1/1
                    # Done
                    shutil.move(src, snk)
                    zapLogxData(WORKPATH, logtype, sfx='.1')
                    _yl.warning(ae, '{} sent    {}'.format(_dt.ut2iso(_dt.locut()), fi1.filename), d=True)
                    _yl.ydataclose()
                    1/1
                1/1

        except Exception as E:
            errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
            DOSQUAWK(errmsg)
            raise
        finally:
            1/1

    #
    # sendWATCHPATHgzs2WORKPATH
    #
    def sendWATCHPATHgzs2WORKPATH():
        1/1
        me = 'sendWATCHPATHgzs2WORKPATH'
        try:

            wfis2 = getFIs(WATCHPATH, 2)
            if wfis2:
                1/1
                swfis2 = [(fi2.modified, fi2) for fi2 in wfis2]
                for (mt, fi2) in sorted(swfis2, key=lambda z: z[0]):
                    1/1
                    ae = fn2ae(fi2.filename)
                    src = os.path.join(WATCHPATH, fi2.filename)
                    if '.logx.' in fi2.filename:
                        1/1
                        # .gz'd *.logx files are uninteresting.
                        os.remove(src)
                        continue
                    snk = os.path.join(WORKPATH, nextWORKSENTfnpfx() + fi2.filename)
                    shutil.move(src, snk)
                    _yl.info(None, '{} -> {}'.format(os.path.split(src)[1], os.path.split(snk)[1]))
                    1/1
                1/1
                sendWORKPATHgzs()
            1/1

        except Exception as E:
            errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
            DOSQUAWK(errmsg)
            raise

    #
    # sendWATCHPATH1s2WORKPATH
    #
    def sendWATCHPATH1s2WORKPATH():
        1/1
        wfis1 = getFIs(WATCHPATH, 1)
        if wfis1:
            1/1
            swfis1 = [(fi1.modified, fi1) for fi1 in wfis1]
            for (mt, fi1) in sorted(swfis1, key=lambda z: z[0]):
                1/1
                src = os.path.join(WATCHPATH, fi1.filename)
                if '.logx.' in src:
                    snk = os.path.join(WORKPATH, fi1.filename)  # No prefix for .logx.1 files.
                else:
                    snk = os.path.join(WORKPATH, nextWORKSENTfnpfx() + fi1.filename)
                shutil.move(src, snk)
                _yl.info(None, '{} -> {}'.format(os.path.split(src)[1], os.path.split(snk)[1]))
                1/1
            1/1
            sendWORKPATH1s()
        1/1

    #
    # incrementallySendLOGs
    #
    def incrementallySendLOGs():        
        1/1
        me = 'incrementallySendLOGs'
        try:

            wfis0 = getFIs(WATCHPATH, 0)
            if wfis0:
                1/1
                for fi0 in wfis0:
                    1/1
                    ae = fn2ae(fi0.filename)
                    logtype = getLogType(fi0.filename)
                    logxdata = getLogxData(WATCHPATH, logtype)
                    if fi0.size < logxdata.size:
                        1/1
                        _m.beep(3)
                        errmsg = 'fi0.size ({}) < logxdata.size ({})'.format(fi0.size, logxdata.size)
                        raise RuntimeError(errmsg)
                        # Or, if POR...
                        _yl.error(None, errmsg)
                        logxdata.sent = 0
                        logxdata.crc = 0
                        logxdata.size = fi0.size
                        1/1
                    ydf_sfx = '-LOG-{}'.format(fi0.filename)
                    if _yl.ydf_sfx[ae] != ydf_sfx:
                        '''...
                        if _yl.ydf_sfx[ae] is not None:
                            _yl.warning(ae, '{} closing'.format(_dt.ut2iso(_dt.locut())), d=True)
                        ...'''
                        _yl.ydataopen(ae, ydf_sfx)
                        _yl.warning(ae, '{} opening {}'.format(_dt.ut2iso(_dt.locut()), fi0.filename), d=True)
                    incrementDynamicFile(ae, fi0, logxdata)
                    putLogxData(logxdata, WATCHPATH, logtype)
                    1/1
                1/1

        except Exception as E:
            errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
            DOSQUAWK(errmsg)
            raise

    #
    # getLogType
    #
    def getLogType(fn):
        """Log filename -> log type ('access' or 'error')."""
        logtype = None
        for z in AELOGTYPES:
            if fn.find(z) in (0, 7):
                logtype = z
                break
        assert logtype, 'no logtype for {}'.format(fn)
        return logtype

    #
    # getLogxData
    #
    def getLogxData(dir, logtype, sfx=''):
        """Get data for *.log file."""
        1/1
        me = 'getLogxData({})'.format(logtype)
        try:
            p = os.path.join(dir, logtype + '.logx' + sfx)
            if not os.path.isfile(p):
                return _ns(modified=0,
                           sent=0,
                           crc=0,
                           size=0,
                           verified=False)
            with open(p, 'rb') as f:
                return pickle.load(f)
        except Exception as E:
            errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
            DOSQUAWK(errmsg)
            raise

    # 
    # putLogxData
    #
    def putLogxData(ld, dir, logtype, sfx=''):
        """Put data for *.log file."""
        1/1
        me = 'putLogxData({})'.format(logtype)
        try:
            p = os.path.join(dir, logtype + '.logx' + sfx)
            with open(p, 'wb') as f:
                pickle.dump(ld, f)
        except Exception as E:
            errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
            DOSQUAWK(errmsg)
            raise
        
    #
    # zapLogxData
    #
    def zapLogxData(dir, logtype, sfx=''):
        """Zap data for *.log file."""
        1/1
        p = os.path.join(dir, logtype + '.logx' + sfx)
        try:    os.remove(p)
        except: pass

    #
    # watchThread   !WT!
    #
    me = 'watcherThread'
    _yl.info(None, me + ' starts')
    try:
        FWTRUNNING = True

        # Inits.
        uu = 0                                                  # Unix Utc. 
        prev_wfis0 = []                                         # prev_wfis0 must exist (and be a list).
        while not FWTSTOP:

            _yl._flush()
           
            # Wait out INTERVAL.                                # !WT!
            z = time.time()
            w = INTERVAL - (z - uu)
            if w > 0:
                _sw.wait(w)
            uu = _dt.utcut()
            ul = _dt.locut(uu)
            uuts = '{:15.4f}'.format(uu)                        # 15.4, unblanked fraction.
            uuiosfs = _dt.ut2isofs(uu)
            uliosfs = _dt.ut2isofs(ul)

            #
            # 0. Send a heartbeat.                          # _dt.ut2iso(_dt.locut(), '~')
            #
            sendHeartbeat()

            #
            # 1. Blocked by a log roll?
            #    Or, do our own controlled log roll?        # <<<
            #
            if checkLogRolling():
                _yl.info(None, 'blocked by log rolling')

            #
            # 2. Send WORKPATH .gz's.
            # 
            sendWORKPATHgzs()

            #
            # 3. Send WORKPATH .1's.
            # 
            sendWORKPATH1s()

            #
            # 4. Send WATCHPATH .gz's to WORKPATH.
            #    Loop to have them processed immediately
            #
            sendWATCHPATHgzs2WORKPATH()

            #
            # 5. Send WATCHPATH .1's to WORKPATH.
            #    Loop to have them processed immediately
            #
            sendWATCHPATH1s2WORKPATH()

            #
            # 6. Incrementally send .log files.
            #    Nginx will eventually turn them into .1's.
            #    Updates a data pickle with progress.
            #
            incrementallySendLOGs()

    except KeyboardInterrupt as E:
        FWTSTOP = True
        # watcherThread:
        _m.beep(1)
        msg = '{}: KI: {}'.format(me, E)
        _yl.warning(None, msg)
        pass    # Let the thread exit.  Avoids "Exception in thread...".
    except Exception as E:
        FWTSTOP = True
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise      
    finally:
        if FWTSTOP:
            FWTSTOPPED = True
        _yl.info(None, '{} exits. STOPPED: {}'.format(me, str(FWTSTOPPED)))
        FWTRUNNING = False
        1/1

#
# getFI
#
def getFI(loc, ft, fn):
    """Return a FileInfo dict for fn."""
    me = 'getFI({})'.format(repr(fn))
    fi = _ns()
    try:
        if   fn.find('access.log') in (0, 7):
            ae = 'a'
        elif fn.find('error.log' ) in (0, 7):
            ae = 'e'
        else:
            return fi
        pfn = os.path.join(location2path(loc), fn)
        try:
            st    = os.stat(pfn)
            size  = st.st_size
            mtime = st.st_mtime
        except:
            # fn possible got renamed
            return fi
        fi.location = loc
        fi.filename = fn
        fi.filetype = ft
        fi.ae       = ae
        fi.modified = mtime
        fi.size     = size
        return fi
    except Exception as E:
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise
    finally:
        1/1

#
# location2path
#
def location2path(loc):
    if   loc in ('watch', WATCHPATH):
        return WATCHPATH
    elif loc in ('work',  WORKPATH):
        return WORKPATH
    elif loc in ('sent',  SENTPATH):
        return SENTPATH
    elif loc in ('ypath', YLOGPATH):
        return YLOGPATH
    else:
        errmsg = 'unknown location: {}'.format(loc)
        raise ValueError(errmsg)

#
# getFIs
#
def getFIs(loc, ft, x=False):
    """Return a list of FileInfo dicts of current files."""
    # loc: watch, work or sent.
    # ft: 0, 1, 2
    me = 'getFIs'
    fis = []
    try:
        for filename in os.listdir(location2path(loc)):
            if not doFilename(ft, filename, x=x):
                continue
            fi = getFI(loc, ft, filename)
            if fi:
                fis.append(fi)
        return fis
    except Exception as E:
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise
    finally:
        1/1

#
# maininits
#
def maininits():
    global gRPFN, gRFILE
    global WATCHPATH, WORKPATH, SENTPATH, INTERVAL, XFILE, YLOGPATH
    global NEXTROLL, ROLLPERIOD, DO_LOGROLL
    me = 'maininits'
    _yl.info(None, me)
    try:

        _a.argSL(_sl)

        gRPFN, gRFILE = _a.argString('rpt', 'report pfn'), None
        if gRPFN:
            gRFILE = open(gRPFN, 'a', encoding=ENCODING, errors=ERRORS)
            _yl._log_file(gRFILE)

        WATCHPATH = _a.argString('watch', 'watch path', WATCHPATH)
        WORKPATH = _a.argString('work', 'work path', WORKPATH)
        SENTPATH = _a.argString('sent', 'sent path', SENTPATH)
        INTERVAL = _a.argFloat('interval', 'cylce interval', INTERVAL)
        XFILE = _a.argString('xfile', 'filename or xlog ip', XFILE)
        YLOGPATH = _a.argString('ypath', 'trace path', YLOGPATH)
        NEXTROLL = _a.argString('nr', 'next roll', NEXTROLL)
        ROLLPERIOD = _a.argString('rp', 'roll period', ROLLPERIOD)
        DO_LOGROLL = bool(ROLLPERIOD)

    except Exception as E:
        errmsg = '{}: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise
    finally:
        1/1

#
# main
#
def main():
    global WATCHPATH, WORKPATH, SENTPATH, YLOGPATH, INTERVAL
    global FWTSTOP, FWTSTOPPED
    global OXLOG, OFILE
    me = 'main'
    watcher_thread = None
    try:
        _yl.info(None, me + ' begins')#$#

        try:    WATCHPATH = os.path.abspath(WATCHPATH)
        except: WATCHPATH = None
        try:    WORKPATH = os.path.abspath(WORKPATH)
        except: WORKPATH = None
        try:    SENTPATH = os.path.abspath(SENTPATH)
        except: SENTPATH = None
        try:    YLOGPATH = os.path.abspath(YLOGPATH)
        except: YLOGPATH = None

        if not os.path.isdir(WATCHPATH):
            errmsg = 'watch path dne: {}'.format(WATCHPATH)
            raise RuntimeError(errmsg)
        if not os.path.isdir(WORKPATH):
            errmsg = 'work path dne: {}'.format(WORKPATH)
            raise RuntimeError(errmsg)
        if not os.path.isdir(SENTPATH):
            errmsg = 'sent path dne: {}'.format(SENTPATH)
            raise RuntimeError(errmsg)

        _yl.info(None)
        _yl.info(None, '    watch: ' + WATCHPATH)
        _yl.info(None, '     work: ' + WORKPATH)
        _yl.info(None, '     sent: ' + SENTPATH)
        _yl.info(None, '    trace: ' + YLOGPATH)
        _yl.info(None, ' interval: ' + str(INTERVAL))
        _yl.info(None)

        # XFILE: output to OXLOG (via host:port) or to a dev/test filename (via OFILE).
        OXLOG = OFILE = None
        host, port = detectHP(XFILE)
        if host and port:
            try:
                OXLOG = XLogTxRx((host, port), txrate=TXRATE)
            except Exception as E:
                errmsg = '{}: cannot create XLogTxRX: {}'.format(me, E)
                DOSQUAWK(errmsg)
                raise
        else:
            try:
                if XFILE:
                    opfn = XFILE
                    if os.path.isfile(opfn):
                        OFILE = open(opfn, 'a', encoding=ENCODING, errors=ERRORS)
                    else:
                        OFILE = open(opfn, 'w', encoding=ENCODING, errors=ERRORS)
            except Exception as E:
                errmsg = '{}: cannot open output file {}: {}'.format(me, opfn, E)
                DOSQUAWK(errmsg)
                raise

        # Start watcher() in a thread.
        watcher_thread = threading.Thread(target=watcherThread)
        watcher_thread.start()
        # Wait for startup.
        while not FWTRUNNING:           
            time.sleep(0.010)          

        # Wait for thread stop.
        while FWTRUNNING:
            time.sleep(1)

        # Ctrl-c to stop & exit.

    except KeyboardInterrupt as E:
        # nl2xlog:
        _m.beep(1)
        msg = '{}: KI: {}'.format(me, E)
        _yl.warning(None, msg)
        pass
    except Exception as E:
        errmsg = '{}: E: {} @ {}'.format(me, E, _m.tblineno())
        DOSQUAWK(errmsg)
        raise             
    finally:
        if watcher_thread and FWTRUNNING:
            FWTSTOP = True
            watcher_thread.join(3 * INTERVAL)
            _yl.info(None, 'thread STOPPED: {}'.format(FWTSTOPPED))
        1/1

if __name__ == '__main__':

    if False:

        ME = _a.get_args(me='HELLO')
        z = copy.copy(_a.ARGS)
        1/1

        ME = _a.get_args(inipfn='MYINIPFN')
        z = copy.copy(_a.ARGS)
        1/1

        ME = _a.get_args(useini=False)
        z = copy.copy(_a.ARGS)
        1/1

        ME = _a.get_args()
        z = copy.copy(_a.ARGS)
        1/1

        1/0

    if False:

        # Test initializing roll time.
        rtdtstr = '16/01/20~10:11'                          # roll time string (24hr)
        print('rtdtstr:', rtdtstr)
        z = justDigits(rtdtstr)
        print('z:', z)
        if len(z) != 10:
            print('must be 10 digits')
            sys.exit(1)
        print('len(z):', len(z))
        rtdt = datetime.datetime.strptime(z, '%y%m%d%H%M')
        rtlu = _dt.utc2loc(time.mktime(rtdt.timetuple()))   # roll time local unix
        print('rtlu:', _dt.ut2iso(rtlu))
        print(' now:', _dt.ut2iso(_dt.locut()))             # now local unix
        1/1
        rpm = 24 * 60                                       # roll period minutes
        print('rpm:', rpm)
        prev_rtlu = rtlu - (rpm * 60)                       # previous roll time local unix
        print('prev_rtlu:', prev_rtlu)
        print('prev_rtlu:', _dt.ut2iso(prev_rtlu))          
        1/1

    if True:

        try:
            ME = _a.get_args()
            ###z = _a.ARGS
            _yl = YLOGGER(_sl)   
            _a.sepBegin(_yl)
            msg = '{} begins'.format(ME)
            _yl.info(None, msg)
            maininits()
            _yl.ylogpath = YLOGPATH
            _yl.ylogopen()
            initRoller()
            main()
            '''...
            if LF:
                _SL.extra(None, '----------------------------------------  {}'.format(_dt.ut2iso(_dt.locut())))
            nl2xlog()
            ...'''
        except KeyboardInterrupt as E:
            # __main__:
            _m.beep(1)
            msg = '{}: KI: {}'.format(ME, E)
            _yl.warning(None, msg)
            pass
        except Exception as E:
            errmsg = '{}: E: {} @ {}'.format(ME, E, _m.tblineno())
            DOSQUAWK(errmsg)
            raise  
        else:
            pass    # No exceptions.           
        finally:
            shutDown()
            '''...
            if LF:
                _SL.extra(None, '========================================  {}'.format(_dt.ut2iso(_dt.locut())))
            ...'''
            msg = '{} ends'.format(ME)
            _yl.info(None, msg)
            _a.sepEnd(_sl)
            try:    gRFILE.close()
            except: pass
            _yl.ylogclose()
            _yl.ydataclose()

    if False:

        try:
            _a.sepBegin(_yl)
            msg = '{} begins'.format(ME)
            _yl.info(None, msg)
            maininits()
            test()
        except KeyboardInterrupt as E:
            # __main__:
            _m.beep(1)
            msg = '{}: KI: {}'.format(ME, E)
            _yl.warning(None, msg)
            pass
        except Exception as E:
            errmsg = '{}: {} @ {}'.format(ME, E, _m.tblineno())
            DOSQUAWK(errmsg)
            raise
        else:
            pass    # No exceptions.           
        finally:
            msg = '{} ends'.format(ME)
            _yl.info(None, msg)
            _a.sepEnd(_sl)
            try:    gRFILE.close()
            except: pass
            1/1

    if False:

        # TEST parseLogrec & making orecs.

        EEL, ESL, SRCID, SUBID = '0', '_', 'TEST', 'test'

        rc, rm, chunks = parseLogrec('a', A0)
        rc, rm, orec, vrec = genACCESSorec(chunks, 'a', EEL, ESL, SRCID, SUBID)
        if rc != 0:
            1/1

        rc, rm, chunks = parseLogrec('a', A2)
        rc, rm, orec, vrec = genACCESSorec(chunks, 'a', EEL, ESL, SRCID, SUBID)
        if rc != 0:
            1/1

        rc, rm, chunks = parseLogrec('a', A4)
        rc, rm, orec, vrec = genACCESSorec(chunks, 'a', EEL, ESL, SRCID, SUBID)
        if rc != 0:
            1/1

        rc, rm, chunks = parseLogrec('a', A6)
        rc, rm, orec, vrec = genACCESSorec(chunks, 'a', EEL, ESL, SRCID, SUBID)
        if rc != 0:
            1/1

        rc, rm, chunks = parseLogrec('e', E0)
        rc, rm, orec, vrec = genERRORorec(chunks, 'e', EEL, ESL, SRCID, SUBID)
        if rc != 0:
            1/1

        rc, rm, chunks = parseLogrec('e', E2)
        rc, rm, orec, vrec = genERRORorec(chunks, 'e', EEL, ESL, SRCID, SUBID)
        if rc != 0:
            1/1

        rc, rm, chunks = parseLogrec('e', E4)
        rc, rm, orec, vrec = genERRORorec(chunks, 'e', EEL, ESL, SRCID, SUBID)
        if rc != 0:
            1/1

        rc, rm, chunks = parseLogrec('e', E6)
        rc, rm, orec, vrec = genERRORorec(chunks, 'e', EEL, ESL, SRCID, SUBID)
        if rc != 0:
            1/1

###
### watch=C:/NL2XLOG/test/ work=C:/NL2XLOG/test/work/ rp=1d fr=1601201545 sent=C:/NL2XLOG/test/sent/ interval=6 xfile=C:/NL2XLOG/test/sent.txt ypath=C:/NL2XLOG/test/ylog/ rpt=C:/NL2XLOG/~me~.rpt
### rp=1d nr=16-01-21~07:30
###

###