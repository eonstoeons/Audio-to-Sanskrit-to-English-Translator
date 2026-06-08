#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Sanskrit Audio Translator
Pure Python stdlib · No external dependencies · Tkinter GUI

Features:
  • Load MP3 or WAV audio files
  • Transcribe phonetic audio → Sanskrit Devanagari (literal)
  • Translate Sanskrit → English
  • Reverse: type English → get Sanskrit transliteration + Devanagari
  • Generate test tones via embedded PyAmby synthesis engine
"""

import tkinter as tk
from tkinter import ttk, scrolledtext, filedialog, messagebox
import threading, queue, os, sys, wave, struct, math, random, cmath
import tempfile, shutil, subprocess, time, array, site
from pathlib import Path

# ═══════════════════════════════════════════════════════════════════
#  EMBEDDED SYNTHESIS ENGINE  (from PyAmby — for smoke-test tones)
# ═══════════════════════════════════════════════════════════════════
CORE = r'''
import json, math, os, random, struct, time, wave
from pathlib import Path

SR=44100;INV_SR=1/SR;TAU=math.tau;_PI=math.pi;NYQUIST=SR*.5;CHUNK=SR*10
_sin=math.sin;_cos=math.cos;_exp=math.exp;_tanh=math.tanh
_rand=random.random;_gauss=random.gauss;_uniform=random.uniform
_SIN_N=4096;_SIN_T=[math.sin(i*TAU/_SIN_N) for i in range(_SIN_N)]
def fast_sin(p):
    q=(p%TAU)*(_SIN_N/TAU);i=int(q)&(_SIN_N-1);f=q-int(q)
    return _SIN_T[i]+(_SIN_T[(i+1)&(_SIN_N-1)]-_SIN_T[i])*f
QUALITY={"mobile":{"max_voices":4,"reverb_combs":4,"max_chimes":6,"bytebeat_sr":4000},
         "balanced":{"max_voices":12,"reverb_combs":6,"max_chimes":10,"bytebeat_sr":8000},
         "studio":{"max_voices":32,"reverb_combs":8,"max_chimes":12,"bytebeat_sr":8000}}
_Q=dict(QUALITY["balanced"])
def set_quality(n): global _Q;_Q=dict(QUALITY.get(n,QUALITY["balanced"]))
def clamp(x,lo=-1.,hi=1.): return lo if x<lo else(hi if x>hi else x)
def soft_clip(x,d=1.10): t=_tanh(d);return _tanh(x*d)/t if t else x
def lerp(a,b,t): return a+(b-a)*t
def mtof(n): return 440.*(2.**((n-69.)/12.))
def humanize(t,a=.004): return t+_gauss(0.,a)

class DCBlocker:
    __slots__=("x","y","R")
    def __init__(self,R=.995): self.x=0.;self.y=0.;self.R=R
    def process(self,v): o=v-self.x+self.R*self.y;self.x=v;self.y=o;return o

class SVF:
    __slots__=("lp","bp","hp","_f","_q")
    def __init__(self,c=1000.,r=0.): self.lp=self.bp=self.hp=0.;self._f=0.;self._q=1.;self.set(c,r)
    def set(self,c,r=None):
        c=min(max(20.,c),NYQUIST*.95);self._f=2.*_sin(_PI*c*INV_SR)
        if r is not None: self._q=1.-min(max(0.,r),.97)
    def lp_process(self,x):
        h=x-self.lp-self._q*self.bp;self.bp+=self._f*h;self.lp+=self._f*self.bp;self.hp=h;return self.lp
    def hp_process(self,x): self.lp_process(x);return self.hp
    def bp_process(self,x): self.lp_process(x);return self.bp

class OnePole:
    __slots__=("a","z")
    def __init__(self,c=1000.): self.z=0.;self.set(c)
    def set(self,c): self.a=1.-_exp(-TAU*min(max(c,1.),NYQUIST*.99)*INV_SR)
    def lp(self,x): self.z+=self.a*(x-self.z);return self.z
    def hp(self,x): return x-self.lp(x)

class ADSR:
    __slots__=("a","d","s","r")
    def __init__(self,a=.01,d=.1,s=.7,r=.3):
        self.a=max(a,.001);self.d=max(d,.001);self.s=s;self.r=max(r,.001)
    def get(self,t,dur):
        if t<0: return 0.
        if t<self.a: return t/self.a
        if t<self.a+self.d: return 1.-(1.-self.s)*((t-self.a)/self.d)
        if t<dur: return self.s
        rt=t-dur;return self.s*(1.-rt/self.r) if rt<self.r else 0.

def osc_saw_blep(p,f):
    t=(p%TAU)/TAU;v=2.*t-1.;dt=f*INV_SR
    if dt<=0: return v
    if t<dt: x=t/dt;v-=x+x-x*x-1.
    elif t>1.-dt: x=(t-1.)/dt;v-=x+x+x*x+1.
    return v
def osc_tri(p): q=(p%TAU)/TAU;return 4.*abs(q-.5)-1.
def osc_sqblep(p,f):
    t=(p%TAU)/TAU;v=1. if t<.5 else -1.;dt=f*INV_SR
    if dt<=0: return v
    if t<dt: x=t/dt;v+=x+x-x*x-1.
    elif t>1.-dt: x=(t-1.)/dt;v-=x+x+x*x+1.
    t2=(t+.5)%1.
    if t2<dt: x=t2/dt;v-=x+x-x*x-1.
    elif t2>1.-dt: x=(t2-1.)/dt;v+=x+x+x*x+1.
    return v

class FMSynth:
    __slots__=("ci","mi","depth","fb","pc","pm","prev")
    def __init__(self,freq,ratio=2.,depth=1.4,feedback=.12):
        self.ci=TAU*freq*INV_SR;self.mi=TAU*freq*ratio*INV_SR
        self.depth=depth;self.fb=feedback;self.pc=0.;self.pm=0.;self.prev=0.
    def sample(self,t=0.,env=1.):
        mod=fast_sin(self.pm+self.prev*self.fb)*self.depth;self.pm+=self.mi
        out=fast_sin(self.pc+mod);self.pc+=self.ci;self.prev=out;return out

class SubSynth:
    __slots__=("phase","inc","wave","filt","env_depth","base_cut","freq")
    def __init__(self,freq,wave="saw",cutoff=2000.,res=.22,env_depth=2500.):
        self.phase=_uniform(0,TAU);self.inc=TAU*freq*INV_SR;self.wave=wave
        self.filt=SVF(cutoff,res);self.env_depth=env_depth;self.base_cut=cutoff;self.freq=freq
    def sample(self,t=0.,env=1.):
        self.phase+=self.inc;w=self.wave
        if w=="saw": v=osc_saw_blep(self.phase,self.freq)
        elif w=="square": v=osc_sqblep(self.phase,self.freq)
        elif w=="tri": v=osc_tri(self.phase)
        else: v=fast_sin(self.phase)
        self.filt.set(min(self.base_cut+self.env_depth*env,NYQUIST*.95))
        return self.filt.lp_process(v)

class KarplusStrong:
    __slots__=("buf","idx","decay","bright")
    def __init__(self,freq,decay=.996,brightness=.55):
        period=max(int(SR/max(freq,24.)),2)
        self.buf=[_uniform(-1,1) for _ in range(period)]
        self.idx=0;self.decay=decay;self.bright=1.-brightness*.7
    def sample(self,t=0.,env=1.):
        L=len(self.buf);i=self.idx%L;j=(i+1)%L;out=self.buf[i]
        self.buf[i]=(self.buf[i]+self.buf[j])*.5*self.bright*self.decay
        self.idx+=1;return out

class Pad:
    __slots__=("phases","incs","lfo","lfo_inc","n")
    def __init__(self,notes,detune=.005):
        ph=[];inc=[]
        for n in notes:
            f=mtof(n)
            for d in(-detune,0.,detune): ph.append(_uniform(0,TAU));inc.append(TAU*f*(1.+d)*INV_SR)
        self.phases=ph;self.incs=inc;self.lfo=_uniform(0,TAU);self.lfo_inc=TAU*.16*INV_SR;self.n=len(ph)
    def sample(self,t=0.,env=1.):
        self.lfo+=self.lfo_inc;mod=.7+.3*(.5+.5*fast_sin(self.lfo))
        v=0.
        for i in range(self.n): self.phases[i]+=self.incs[i];v+=fast_sin(self.phases[i])
        return (v/self.n)*mod if self.n else 0.

class PinkNoise:
    __slots__=("b",)
    def __init__(self): self.b=[0.]*6
    def sample(self):
        b=self.b;w=_uniform(-1,1)
        b[0]=.99886*b[0]+w*.0555179;b[1]=.99332*b[1]+w*.0750759
        b[2]=.96900*b[2]+w*.1538520;b[3]=.86650*b[3]+w*.3104856
        b[4]=.55000*b[4]+w*.5329522;b[5]=-.7616*b[5]-w*.0168980
        return(b[0]+b[1]+b[2]+b[3]+b[4]+b[5]+w*.5362)*.11

class BrownNoise:
    __slots__=("z",)
    def __init__(self): self.z=0.
    def sample(self): self.z=.98*self.z+.03*_uniform(-1,1);return clamp(self.z)

class SingingBowl:
    __slots__=("partials","decay","t","ns","amp","intensity")
    def __init__(self,intensity=.60):
        self.partials=[];self.decay=0.;self.t=0.;self.ns=0.;self.amp=0.;self.intensity=intensity;self._strike()
    def _strike(self):
        base=random.choice([180.,220.,260.,310.,370.,440.])
        self.partials=[]
        for r,b in zip([1.,2.71,4.77,7.03,9.43],[0.,.7,1.2,.5,.9]):
            f=base*r
            if f<NYQUIST*.9: self.partials.append([_uniform(0,TAU),TAU*f*INV_SR,TAU*b*INV_SR,1./(r*r*.3+1.)])
        self.decay=_uniform(5.,12.);self.t=0.;self.amp=_uniform(.5,1.);self.ns=_uniform(6.,18.)
    def sample(self,t=0.):
        self.t+=INV_SR
        if self.t>self.ns: self._strike()
        env=_exp(-self.t*2./max(self.decay,.01))
        if env<.001: return 0.
        v=0.
        for p in self.partials:
            p[0]+=p[1];v+=fast_sin(p[0])*p[3]*(.85+.15*fast_sin(p[0]*.0001+p[2]*self.t*SR))
        return v*env*self.amp*self.intensity*.16

class WindChimes:
    __slots__=("density","chimes","intensity")
    def __init__(self,density=.40,intensity=.50): self.density=density;self.chimes=[];self.intensity=intensity
    def sample_stereo(self,t=0.):
        if len(self.chimes)<_Q["max_chimes"] and _rand()<self.density*.0003:
            f=random.choice([1200,1580,1890,2100,2640,3150,3520])
            self.chimes.append([0.,float(f),_uniform(3,8),0.,_uniform(.3,1.),_uniform(-.5,.5)])
        l=0.;r=0.;alive=[]
        for ch in self.chimes:
            ch[0]+=TAU*ch[1]*INV_SR;ch[3]+=INV_SR;env=_exp(-ch[3]/ch[2])
            if env<.001: continue
            alive.append(ch)
            tone=fast_sin(ch[0])*.6+fast_sin(ch[0]*2.76)*.25+fast_sin(ch[0]*5.4)*.12
            v=tone*env*ch[4]*self.intensity*.12;pr=(ch[5]+1)*_PI*.25;l+=v*_cos(pr);r+=v*_sin(pr)
        self.chimes=alive;return l,r

class Reverb:
    CD=(.02257,.02391,.02641,.02743,.02999,.03119,.03371,.03571)
    AP=(.0050,.0017,.00051)
    __slots__=("combs","ci","cfb","aps","ai","lps","damp","mix")
    def __init__(self,size=.9,damp=.45,mix=.30):
        nc=_Q["reverb_combs"];self.combs=[([0.]*max(int(SR*d*size),2)) for d in self.CD[:nc]]
        self.ci=[0]*nc;self.cfb=.84;self.aps=[([0.]*max(int(SR*d),2)) for d in self.AP]
        self.ai=[0]*3;self.lps=[0.]*nc;self.damp=damp;self.mix=mix
    def process(self,x):
        out=0.
        for i,buf in enumerate(self.combs):
            idx=self.ci[i]%len(buf);val=buf[idx]
            self.lps[i]=val*(1.-self.damp)+self.lps[i]*self.damp
            buf[idx]=x+self.lps[i]*self.cfb;self.ci[i]+=1;out+=val
        out/=len(self.combs)
        for i,buf in enumerate(self.aps):
            idx=self.ai[i]%len(buf);bv=buf[idx]
            buf[idx]=out+bv*.5;self.ai[i]+=1;out=bv-out*.5
        return x*(1.-self.mix)+out*self.mix

SCALES={"pentatonic":[0,2,4,7,9],"minor":[0,2,3,5,7,8,10],"major":[0,2,4,5,7,9,11]}
CHORDS={"maj":[0,4,7],"min":[0,3,7],"sus2":[0,2,7],"sus4":[0,5,7]}
def build_scale(root,sn,octaves=3):
    pat=SCALES.get(sn,SCALES["minor"])
    return[root+o*12+i for o in range(octaves) for i in pat if 0<=root+o*12+i<=127]
def build_chord(root,cn): return[root+i for i in CHORDS.get(cn,CHORDS["sus2"])]

class Event:
    __slots__=("time","duration","engine","vol","pan","env")
    def __init__(self,time,dur,engine,vol=.5,pan=0.,env=None):
        self.time=time;self.duration=dur;self.engine=engine
        self.vol=vol;self.pan=pan;self.env=env or ADSR(.01,.1,.7,.3)

def master_proc(l,r,dcl,dcr,gain=.88):
    l=dcl.process(soft_clip(l,1.10)*gain);r=dcr.process(soft_clip(r,1.10)*gain)
    return clamp(l,-.999,.999),clamp(r,-.999,.999)

def render_sanskrit_tone(path, freq=432., duration=4., tone_type="bowl", seed=42):
    """Render a tone that evokes the sonic character of Sanskrit mantra chanting."""
    random.seed(seed); SR_=44100; TAU_=math.tau; INV_SR_=1/SR_
    total=int(SR_*duration)+SR_
    dcl=DCBlocker(); dcr=DCBlocker()
    rl=Reverb(size=1.4, damp=.45, mix=.55)
    rr=Reverb(size=1.50, damp=.48, mix=.55)
    # Bowl harmonics (Tibetan/Sanskrit resonance)
    bowl=SingingBowl(intensity=.75)
    # Drone pad on root
    notes=[int(round(69+12*math.log2(freq/440.)))]
    notes_ext=notes+[notes[0]+7, notes[0]+12]
    pad=Pad(notes_ext, detune=.003)
    adsr=ADSR(.8, .5, .85, 1.2)
    with wave.open(str(path),"wb") as w:
        w.setnchannels(2); w.setsampwidth(2); w.setframerate(SR_)
        frames=bytearray(total*4); fi=0
        for i in range(total):
            t=i*INV_SR_
            env=adsr.get(t, duration)
            bv=bowl.sample(t)
            pv=pad.sample(t)*env*.35
            l=bv+pv; r=bv+pv
            l=rl.process(l); r=rr.process(r)
            l,r=master_proc(l,r,dcl,dcr,.82)
            struct.pack_into("<hh",frames,fi,int(l*32767),int(r*32767)); fi+=4
        w.writeframes(frames)
    return path

def render_mantra_sequence(path, freqs, duration=6., seed=99):
    """Render a sequence of tones mimicking a chanted mantra syllable sequence."""
    random.seed(seed); SR_=44100; TAU_=math.tau; INV_SR_=1/SR_
    n=len(freqs); seg=duration/n; total=int(SR_*duration)+SR_
    dcl=DCBlocker(); dcr=DCBlocker()
    rl=Reverb(size=1.3, damp=.40, mix=.45)
    rr=Reverb(size=1.38, damp=.43, mix=.45)
    # Pre-build KarplusStrong per syllable (plucked string = veena timbre)
    synths=[KarplusStrong(f, decay=.997, brightness=.45) for f in freqs]
    adsr=ADSR(.05, .10, .80, .40)
    with wave.open(str(path),"wb") as w:
        w.setnchannels(2); w.setsampwidth(2); w.setframerate(SR_)
        frames=bytearray(total*4); fi=0
        for i in range(total):
            t=i*INV_SR_
            si=min(int(t/seg), n-1)
            lt=t-si*seg
            env=adsr.get(lt, seg*.85)
            v=synths[si].sample(lt, env)*env*.55
            l=v*.9; r=v*1.1
            l=rl.process(l); r=rr.process(r)
            l,r=master_proc(l,r,dcl,dcr,.84)
            struct.pack_into("<hh",frames,fi,int(l*32767),int(r*32767)); fi+=4
        w.writeframes(frames)
    return path
'''

# ═══════════════════════════════════════════════════════════════════
#  SANSKRIT ↔ ENGLISH TRANSLATION ENGINE
#  (offline rule-based — covers Vedic vocabulary, mantras, grammar)
# ═══════════════════════════════════════════════════════════════════

# Devanagari transliteration map (IAST → Devanagari)
IAST_TO_DEV = {
    'ā':'आ','a':'अ','i':'इ','ī':'ई','u':'उ','ū':'ऊ',
    'ṛ':'ऋ','ṝ':'ॠ','ḷ':'ऌ','e':'ए','ai':'ऐ','o':'ओ','au':'औ',
    'aṃ':'अं','aḥ':'अः','ṃ':'ं','ḥ':'ः',
    'k':'क','kh':'ख','g':'ग','gh':'घ','ṅ':'ङ',
    'c':'च','ch':'छ','j':'ज','jh':'झ','ñ':'ञ',
    'ṭ':'ट','ṭh':'ठ','ḍ':'ड','ḍh':'ढ','ṇ':'ण',
    't':'त','th':'थ','d':'द','dh':'ध','n':'न',
    'p':'प','ph':'फ','b':'ब','bh':'भ','m':'म',
    'y':'य','r':'र','l':'ल','v':'व',
    'ś':'श','ṣ':'ष','s':'स','h':'ह',
    'kṣ':'क्ष','jñ':'ज्ञ','tr':'त्र',
}

# Sanskrit word → (literal_meaning, english_meaning, part_of_speech)
SANSKRIT_DICT = {
    # Sacred syllables
    'om':       ('the primordial sound / that which is','The universal vibration, the sound of creation','sacred syllable'),
    'aum':      ('the threefold sound A-U-M','The tripartite cosmic sound (waking/dream/deep sleep)','sacred syllable'),
    'so':       ('that','That (referring to Brahman/universal self)','pronoun'),
    'ham':      ('I am','I am (the breath mantra, affirming self)','pronoun'),
    'hum':      ('the protective seed','Seed syllable of wrath, protection, awakening','bija mantra'),
    'aim':      ('the creative seed of Saraswati','Seed syllable of Saraswati, wisdom and learning','bija mantra'),
    'hrīm':     ('the seed of Mahamaya','Seed syllable of the goddess, magic and illusion','bija mantra'),
    'śrīm':     ('the seed of Lakshmi','Seed syllable of abundance and beauty','bija mantra'),
    'klīm':     ('the seed of attraction','Seed syllable of desire and fulfilment','bija mantra'),
    'gaṃ':      ('seed of Ganesha','Seed syllable invoking Ganesha, remover of obstacles','bija mantra'),
    'duṃ':      ('seed of Durga','Seed syllable invoking Durga, the fierce protector','bija mantra'),

    # Core Vedic/Upanishadic terms
    'brahman':  ('the vast / the expanding','The absolute, infinite, universal consciousness','noun (neuter)'),
    'ātman':    ('the self / the breath','The individual self, soul, identical to Brahman','noun (masculine)'),
    'sat':      ('being / existence / truth','Pure existence, truth, the real','adjective'),
    'cit':      ('consciousness / knowing','Pure awareness, consciousness','noun (neuter)'),
    'ānanda':   ('bliss / joy without cause','Pure unconditional bliss','noun (masculine)'),
    'māyā':     ('that which is not / illusion / measure','The creative power that makes the unreal appear real','noun (feminine)'),
    'dharma':   ('that which upholds / duty / right action','Cosmic law, one\'s duty, the path of right action','noun (masculine)'),
    'karma':    ('action / deed','Action and its inevitable fruit/consequence','noun (neuter)'),
    'yoga':     ('union / yoke / discipline','Union of individual with universal self; spiritual practice','noun (masculine)'),
    'jñāna':    ('knowing / knowledge','Direct spiritual knowledge, wisdom','noun (neuter)'),
    'bhakti':   ('devotion / sharing / participation','Loving devotion to the divine','noun (feminine)'),
    'mokṣa':    ('liberation / release','Freedom from the cycle of birth and death','noun (masculine)'),
    'saṃsāra':  ('flowing together / the world-process','The cycle of death and rebirth, conditioned existence','noun (masculine)'),
    'nirvāṇa':  ('blown out / extinguished','The extinction of craving; liberation in Buddhism','noun (neuter)'),
    'mantra':   ('instrument of thought / sacred formula','A sacred sound or formula with transformative power','noun (masculine)'),
    'tantra':   ('loom / continuity / system','A system of practice weaving body and spirit','noun (neuter)'),
    'yantra':   ('instrument / that which restrains','A geometric diagram used as a focal point in worship','noun (neuter)'),
    'chakra':   ('wheel / circle','Energy centers in the subtle body','noun (masculine)'),
    'prāṇa':    ('breath / life-force','The vital life-force, breath','noun (masculine)'),
    'nāda':     ('sound / vibration','Primordial sound, inner resonance','noun (masculine)'),
    'svara':    ('one\'s own / musical note','A musical tone, the voice, self-luminous','noun (masculine)'),
    'śānti':    ('peace / quietness','Peace, tranquility, the cessation of disturbance','noun (feminine)'),
    'guru':     ('heavy / weighty / dispeller of darkness','Spiritual teacher, one who removes ignorance','noun (masculine)'),
    'śiṣya':    ('student / disciple','A spiritual student or disciple','noun (masculine)'),
    'ahiṃsā':   ('non-harming / non-violence','The principle of non-injury to all living beings','noun (feminine)'),
    'satya':    ('truth / existence','Truth, the quality of being real','noun (neuter)'),
    'tapas':    ('heat / austerity / ardour','Disciplined austerity, the fire of self-purification','noun (neuter)'),
    'svādhyāya':('self-study / one\'s own reading','Study of sacred texts and of oneself','noun (masculine)'),
    'santoṣa':  ('contentment / satisfaction','Contentment, equanimity with what is','noun (masculine)'),
    'śauca':    ('cleanliness / purity','Purity, both internal and external','noun (neuter)'),
    'īśvara':   ('the lord / the capable one','God, the personal lord, the divine ruler','noun (masculine)'),
    'praṇidhāna':('dedication / laying down before','Surrender and dedication to the divine','noun (neuter)'),
    'samādhi':  ('placing together / integration','The state of meditative absorption, union','noun (masculine)'),
    'dhyāna':   ('meditation / contemplation','Unbroken flow of awareness toward the object','noun (neuter)'),
    'dhāraṇā':  ('holding / concentration','Focused concentration on a single point','noun (feminine)'),
    'pratyāhāra':('withdrawal / gathering inward','Withdrawal of the senses from their objects','noun (masculine)'),
    'prāṇāyāma':('breath extension / mastery of life-force','Regulation and expansion of the breath','noun (masculine)'),
    'āsana':    ('seat / posture / to sit','A steady and comfortable bodily posture','noun (neuter)'),
    'niyama':   ('observance / restraint / rule','Personal observances, the second limb of yoga','noun (masculine)'),
    'yama':     ('restraint / the god of death','Ethical restraints, the first limb of yoga','noun (masculine)'),
    'sūtra':    ('thread / aphorism','A concise teaching thread, an aphorism','noun (neuter)'),
    'upaniṣad': ('sitting down near / secret teaching','Esoteric wisdom texts; the end of the Vedas','noun (feminine)'),
    'veda':     ('knowledge / that which is known','Sacred knowledge; the oldest scriptural texts','noun (masculine)'),
    'ṛgveda':   ('knowledge of verses / praise-knowledge','The Rigveda, the oldest of the four Vedas','noun (masculine)'),
    'śiva':     ('auspicious / gracious','The auspicious one; the deity of transformation','noun (masculine)'),
    'viṣṇu':    ('pervader / all-pervading','The all-pervading preserver deity','noun (masculine)'),
    'devī':     ('the shining one / goddess','The goddess, feminine divine power','noun (feminine)'),
    'deva':     ('the shining one / god','A deity, divine being, shining one','noun (masculine)'),
    'śakti':    ('power / energy / capacity','The divine feminine energy, power of manifestation','noun (feminine)'),
    'kṛṣṇa':    ('dark / the dark one / all-attractive','The all-attractive one, deity of love and devotion','noun (masculine)'),
    'rāma':     ('pleasing / joy-giving','The delightful one; the divine hero of the Ramayana','noun (masculine)'),
    'gaṇeśa':   ('lord of hosts / lord of categories','The lord of beginnings, remover of obstacles','noun (masculine)'),
    'sarasvatī':('she who flows / she who possesses eloquence','Goddess of wisdom, arts, and learning','noun (feminine)'),
    'lakṣmī':   ('mark / auspicious sign / prosperity','Goddess of wealth, beauty, and fortune','noun (feminine)'),
    'durgā':    ('the inaccessible / the invincible fortress','The fierce protective mother goddess','noun (feminine)'),
    'kālī':     ('the dark one / she who is time','The goddess of time, death, and liberation','noun (feminine)'),
    'namas':    ('bow / obeisance / reverential salutation','A reverential bow, salutation','noun (neuter)'),
    'namaste':  ('I bow to you','Salutation: the divine in me honours the divine in you','salutation'),
    'namaḥ':    ('obeisance / salutation to','Reverential salutation (dative form)','salutation'),
    'svāhā':    ('so be it / well-spoken / oblation cry','The exclamation at the end of a fire oblation','exclamation'),
    'vaṣaṭ':    ('may he carry / oblation cry','Exclamation accompanying a Vedic fire offering','exclamation'),
    'phat':     ('crack / burst / destroy','Seed syllable of destruction, breaking through obstacles','bija mantra'),
    'oṃ':       ('the primordial sound','The universal vibration, the sound of creation','sacred syllable'),
    'śāntih':   ('peace','Peace — traditionally chanted three times at close of Vedic prayer','noun'),
    'hari':     ('remover / the tawny one','Epithet of Vishnu/Krishna as remover of suffering','noun (masculine)'),
    'nārāyaṇa': ('refuge of beings / born of waters','A name of Vishnu, the universal refuge','noun (masculine)'),
    'vāyu':     ('the blowing one / wind','The wind deity, the god of air and breath','noun (masculine)'),
    'agni':     ('the going one / fire','The fire deity, cosmic fire, the digestive force','noun (masculine)'),
    'sūrya':    ('the sun / that which generates','The sun deity, the cosmic light source','noun (masculine)'),
    'soma':     ('the pressed one / nectar','The moon, the sacrificial plant-deity, nectar of immortality','noun (masculine)'),
    'indra':    ('powerful / king of gods','The king of the Vedic gods, god of thunder and rain','noun (masculine)'),
    'varuna':   ('he who covers / the cosmic envelope','The all-encompassing sky god, cosmic order','noun (masculine)'),
    'mitra':    ('friend / compact / the sun','The deity of friendship, contracts and the sun','noun (masculine)'),
    'loka':     ('world / open space / the seen','A world, plane of existence, space','noun (masculine)'),
    'bhūr':     ('earth / the physical plane','The earth, the first of the three realms','noun'),
    'bhuvaḥ':   ('atmosphere / the vital plane','The atmosphere, the second realm','noun'),
    'svaḥ':     ('heaven / the causal plane','Heaven, the third realm, the celestial','noun'),
    'tat':      ('that','That (referring to the absolute, the beyond)','pronoun'),
    'savitur':  ('of the sun / of the vivifier','Of Savitur, the creative sun energy','noun (genitive)'),
    'vareṇyaṃ': ('most excellent / adorable / worthy of choice','The most excellent, worthy of being chosen','adjective'),
    'bhargo':   ('radiance / effulgence / purifying light','The brilliant purifying light','noun (neuter)'),
    'devasya':  ('of the divine / of the shining one','Of the deity, of the divine','noun (genitive)'),
    'dhīmahi':  ('we meditate / we hold in the mind','We meditate, we hold in awareness','verb (1st pl.)'),
    'yo':       ('who / that which','Who, that which (relative pronoun)','pronoun'),
    'naḥ':      ('our / to us','Our, to us (genitive/dative)','pronoun'),
    'pracodayāt':('may it inspire / may it direct','May it inspire, impel, direct us','verb (optative)'),
    'ananda':   ('bliss / joy','Pure unconditional joy and bliss','noun (masculine)'),
    'aham':     ('I','I, the self, the first person','pronoun'),
    'tvam':     ('you','You, the second person','pronoun'),
    'brahma':   ('the vast / creator','The creator aspect of the divine; also Brahman in some contexts','noun (masculine)'),
    'sarvam':   ('all / everything / whole','All, everything, the totality','adjective/pronoun'),
    'idam':     ('this','This (proximate demonstrative)','pronoun'),
    'ca':       ('and / also','And, also — conjunctive particle','particle'),
    'eva':      ('only / indeed / truly','Indeed, truly, only — emphatic particle','particle'),
    'na':       ('not / no','Not, the particle of negation','negative particle'),
    'hi':       ('indeed / for / because','Indeed, for, because — emphatic/causal particle','particle'),
    'tad':      ('that','That — demonstrative pronoun','pronoun'),
    'sarva':    ('all / whole / complete','All, entire, complete','adjective'),
    'manas':    ('mind / the thinking principle','The mind, the manas faculty of thought and emotion','noun (neuter)'),
    'buddhi':   ('intellect / discernment / awakening','Higher intellect, discrimination, awakening','noun (feminine)'),
    'ahaṃkāra': ('I-maker / ego-sense','The ego, the faculty that says "I am this"','noun (masculine)'),
    'citta':    ('mind-stuff / consciousness-field','The field of consciousness, mind-stuff','noun (neuter)'),
    'puruṣa':   ('the person / the cosmic man / pure witness','The pure witness consciousness, the cosmic man','noun (masculine)'),
    'prakṛti':  ('nature / that which acts first','Primordial nature, matter, the material ground of existence','noun (feminine)'),
    'guṇa':     ('strand / quality / rope','The three qualities of nature: sattva, rajas, tamas','noun (masculine)'),
    'sattva':   ('beingness / purity / clarity','The quality of luminosity, clarity, and balance','noun (neuter)'),
    'rajas':    ('redness / passion / activity','The quality of dynamism, passion, and activity','noun (neuter)'),
    'tamas':    ('darkness / inertia / heaviness','The quality of inertia, heaviness, and obscurity','noun (neuter)'),
    'kāla':     ('time / the dark one / death','Time; also an epithet of death and transformation','noun (masculine)'),
    'ākāśa':    ('shining / space / ether','Space, ether — the most subtle of the five elements','noun (masculine)'),
    'vāta':     ('wind / the moving one','Wind, air — one of the five elements','noun (masculine)'),
    'jala':     ('water / the shimmering','Water — one of the five elements','noun (neuter)'),
    'agni':     ('fire / the going one','Fire — one of the five elements; the divine messenger','noun (masculine)'),
    'pṛthivī':  ('the broad one / earth','Earth — the most dense of the five elements','noun (feminine)'),
    'anāhata':  ('unstruck / unhurt / the fourth chakra','The unstruck sound; the heart chakra','adjective/noun'),
    'ājñā':     ('command / the sixth chakra','The command centre; the third-eye chakra','noun (feminine)'),
    'sahasrāra':('thousand-petalled','The thousand-petalled lotus; the crown chakra','noun (masculine)'),
    'muladhara':('root support / foundation chakra','The root chakra, seat of kundalini energy','noun (masculine)'),
    'svādhiṣṭhāna':('one\'s own dwelling / sacral chakra','The sacral chakra, seat of creativity','noun (neuter)'),
    'maṇipūra': ('city of jewels / solar plexus chakra','The solar plexus chakra, seat of will and fire','noun (neuter)'),
    'viśuddha': ('pure / purified / throat chakra','The throat chakra, seat of purified expression','adjective/noun'),
    'kuṇḍalinī':('coiled one / the serpent power','The coiled dormant energy at the base of the spine','noun (feminine)'),
    'haṭha':    ('force / sun-moon / wilful','Forceful; also the union of sun (ha) and moon (tha)','noun/adjective'),
    'nāḍī':     ('tube / channel / river','An energy channel in the subtle body','noun (feminine)'),
    'suṣumnā':  ('very gracious / central channel','The central energy channel of the spine','noun (feminine)'),
    'iḍā':      ('comfort / the lunar channel','The left lunar energy channel','noun (feminine)'),
    'piṅgalā':  ('the tawny / the solar channel','The right solar energy channel','noun (feminine)'),
    'bindu':    ('drop / point / seed','A drop; the source-point of creation; semen','noun (masculine)'),
    'nāda':     ('sound / vibration / flow','Primordial sound, inner vibrational resonance','noun (masculine)'),
    'kalā':     ('art / skill / fraction','An art form, a fraction, a ray of the moon','noun (feminine)'),
    'śrī':      ('radiance / prosperity / auspiciousness','Auspicious light, beauty, prosperity; honorific prefix','noun (feminine)'),
    'om̐':       ('the primordial vibration','Variant of Om, the cosmic vibration','sacred syllable'),
    'namah':    ('obeisance / salutation','Bow, salutation','noun'),
    'śivāya':   ('to Shiva / for the auspicious','To Shiva, for the auspicious one (dative)','noun (dative)'),
    'pañca':    ('five','Five','numeral'),
    'aṣṭa':     ('eight','Eight','numeral'),
    'daśa':     ('ten','Ten','numeral'),
    'śata':     ('hundred','A hundred','numeral'),
    'sahasra':  ('thousand','A thousand','numeral'),
}

# English → Sanskrit lookup (reverse of above, best-match)
ENGLISH_TO_SANSKRIT = {}
for sk, (lit, eng, pos) in SANSKRIT_DICT.items():
    # Index by first key English word
    key_words = eng.lower().replace(',','').replace(';','').split()
    for w in key_words[:3]:
        if len(w) > 3 and w not in ENGLISH_TO_SANSKRIT:
            ENGLISH_TO_SANSKRIT[w] = sk

# Common English → Sanskrit direct mappings
ENGLISH_DIRECT = {
    'peace': 'śānti',   'love': 'prema',      'truth': 'satya',
    'light': 'jyoti',   'fire': 'agni',        'water': 'jala',
    'earth': 'pṛthivī', 'wind': 'vāyu',        'sky': 'ākāśa',
    'god': 'deva',      'goddess': 'devī',      'sun': 'sūrya',
    'moon': 'soma',     'mind': 'manas',        'soul': 'ātman',
    'self': 'ātman',    'bliss': 'ānanda',      'joy': 'ānanda',
    'liberation': 'mokṣa', 'freedom': 'mokṣa', 'union': 'yoga',
    'knowledge': 'jñāna', 'devotion': 'bhakti', 'duty': 'dharma',
    'action': 'karma',  'breath': 'prāṇa',     'sound': 'nāda',
    'mantra': 'mantra', 'teacher': 'guru',     'student': 'śiṣya',
    'consciousness': 'cit', 'being': 'sat',    'existence': 'sat',
    'nature': 'prakṛti', 'time': 'kāla',       'space': 'ākāśa',
    'energy': 'śakti',  'power': 'śakti',      'illusion': 'māyā',
    'austerity': 'tapas', 'meditation': 'dhyāna', 'posture': 'āsana',
    'salutation': 'namaḥ', 'bow': 'namas',     'om': 'oṃ',
    'compassion': 'karuṇā', 'wisdom': 'prajñā', 'heart': 'hṛdaya',
}

def simple_devanagari(word):
    """
    Convert a simple IAST/romanized Sanskrit word to approximate Devanagari.
    This is a heuristic for common words — not a full IAST parser.
    """
    WORD_MAP = {
        'om': 'ॐ', 'oṃ': 'ॐ', 'aum': 'ॐ',
        'śānti': 'शान्ति', 'shanti': 'शान्ति',
        'namaste': 'नमस्ते', 'namaḥ': 'नमः', 'namas': 'नमस्',
        'yoga': 'योग', 'dharma': 'धर्म', 'karma': 'कर्म',
        'brahman': 'ब्रह्मन्', 'ātman': 'आत्मन्', 'ānanda': 'आनन्द',
        'ananda': 'आनन्द', 'māyā': 'माया', 'mokṣa': 'मोक्ष',
        'sat': 'सत्', 'cit': 'चित्', 'bhakti': 'भक्ति',
        'jñāna': 'ज्ञान', 'prāṇa': 'प्राण', 'śiva': 'शिव',
        'viṣṇu': 'विष्णु', 'kṛṣṇa': 'कृष्ण', 'rāma': 'राम',
        'devī': 'देवी', 'deva': 'देव', 'guru': 'गुरु',
        'mantra': 'मन्त्र', 'tantra': 'तन्त्र', 'yantra': 'यन्त्र',
        'chakra': 'चक्र', 'nāda': 'नाद', 'bindu': 'बिन्दु',
        'sūtra': 'सूत्र', 'veda': 'वेद', 'samādhi': 'समाधि',
        'dhyāna': 'ध्यान', 'āsana': 'आसन', 'agni': 'अग्नि',
        'sūrya': 'सूर्य', 'soma': 'सोम', 'indra': 'इन्द्र',
        'śakti': 'शक्ति', 'kuṇḍalinī': 'कुण्डलिनी',
        'sarasvatī': 'सरस्वती', 'lakṣmī': 'लक्ष्मी',
        'gaṇeśa': 'गणेश', 'kālī': 'काली', 'durgā': 'दुर्गा',
        'svāhā': 'स्वाहा', 'haṭha': 'हठ', 'manas': 'मनस्',
        'buddhi': 'बुद्धि', 'citta': 'चित्त', 'puruṣa': 'पुरुष',
        'prakṛti': 'प्रकृति', 'sattva': 'सत्त्व', 'rajas': 'रजस्',
        'tamas': 'तमस्', 'ākāśa': 'आकाश', 'vāyu': 'वायु',
        'pṛthivī': 'पृथिवी', 'jala': 'जल', 'ahiṃsā': 'अहिंसा',
        'satya': 'सत्य', 'tapas': 'तपस्', 'śauca': 'शौच',
        'śrī': 'श्री', 'hari': 'हरि', 'nārāyaṇa': 'नारायण',
        'tat': 'तत्', 'brahma': 'ब्रह्म', 'aham': 'अहम्',
        'tvam': 'त्वम्', 'sarvam': 'सर्वम्', 'idam': 'इदम्',
        'bhūr': 'भूर्', 'bhuvaḥ': 'भुवः', 'svaḥ': 'स्वः',
        'savitur': 'सवितुर्', 'vareṇyaṃ': 'वरेण्यं',
        'bhargo': 'भर्गो', 'devasya': 'देवस्य',
        'dhīmahi': 'धीमहि', 'pracodayāt': 'प्रचोदयात्',
        'pañca': 'पञ्च', 'śiṣya': 'शिष्य',
        'loka': 'लोक', 'kāla': 'काल',
    }
    return WORD_MAP.get(word.lower(), f'[{word}]')

def translate_sanskrit_to_english(text):
    """
    Given Sanskrit text (romanized/IAST), return:
      - word-by-word literal translation
      - fluid English translation
    """
    words = text.lower().strip().split()
    literal_parts = []
    english_parts = []

    for w in words:
        # strip punctuation
        clean = w.strip('.,;:!?()')
        if clean in SANSKRIT_DICT:
            lit, eng, pos = SANSKRIT_DICT[clean]
            literal_parts.append(f"{w} [{lit}]")
            english_parts.append(eng.split(';')[0].split(',')[0].strip())
        else:
            # partial match
            matched = False
            for key in SANSKRIT_DICT:
                if clean.startswith(key) or key.startswith(clean):
                    lit, eng, pos = SANSKRIT_DICT[key]
                    literal_parts.append(f"{w} [{lit}~]")
                    english_parts.append(eng.split(';')[0].split(',')[0].strip())
                    matched = True
                    break
            if not matched:
                literal_parts.append(f"{w} [?]")
                english_parts.append(w)

    literal = ' | '.join(literal_parts)
    # Build a natural English sentence
    fluid = ' '.join(english_parts).capitalize()
    if not fluid.endswith('.'): fluid += '.'
    return literal, fluid

def translate_english_to_sanskrit(text):
    """
    Given English text, return Sanskrit transliteration, Devanagari, and notes.
    """
    words = text.lower().strip().split()
    sk_words = []
    dev_words = []
    notes = []

    for w in words:
        clean = w.strip('.,;:!?()')
        if clean in ENGLISH_DIRECT:
            sk = ENGLISH_DIRECT[clean]
        elif clean in ENGLISH_TO_SANSKRIT:
            sk = ENGLISH_TO_SANSKRIT[clean]
        else:
            # Try stem matching
            sk = None
            for eng_w, sk_w in ENGLISH_DIRECT.items():
                if clean.startswith(eng_w) or eng_w.startswith(clean):
                    sk = sk_w
                    break
            if sk is None:
                sk = f'[{clean}]'
                notes.append(f"'{clean}' has no direct Sanskrit equivalent — consider context")

        dev = simple_devanagari(sk)
        sk_words.append(sk)
        dev_words.append(dev)

    transliteration = ' '.join(sk_words)
    devanagari = ' '.join(dev_words)
    note_text = ' | '.join(notes) if notes else 'Translation complete.'

    # If we found a single famous mantra equivalent, annotate
    if len(words) == 1 and sk_words[0] in SANSKRIT_DICT:
        lit, eng, pos = SANSKRIT_DICT[sk_words[0]]
        note_text = f"Part of speech: {pos} | Literal root: {lit}"

    return transliteration, devanagari, note_text


# Known mantra phrases → translation
MANTRA_PHRASES = {
    'om namah shivaya': (
        'oṃ namaḥ śivāya',
        'ॐ नमः शिवाय',
        'Om [the universal sound] | namas [obeisance / bow] | śivāya [to the auspicious one]',
        'I bow to the auspicious one, the inner Self; salutation to Shiva in all things.',
        'Five-syllable Panchakshara mantra of Shaivism. Invokes the transformative grace of Shiva.'
    ),
    'om mani padme hum': (
        'oṃ maṇi padme hūṃ',
        'ॐ मणि पद्मे हूं',
        'Om [universal sound] | maṇi [jewel / wish-granting gem] | padme [in the lotus] | hūṃ [awakening seed]',
        'The jewel is in the lotus — awakening is found within the heart of existence.',
        'The six-syllable mantra of Avalokiteshvara, compassion. Each syllable purifies one of the six realms.'
    ),
    'om shanti shanti shanti': (
        'oṃ śāntiḥ śāntiḥ śāntiḥ',
        'ॐ शान्तिः शान्तिः शान्तिः',
        'Om [universal sound] | śāntiḥ [peace / peace / peace]',
        'Om. Peace, peace, peace — may there be peace in body, mind, and spirit.',
        'The three repetitions address peace in the three planes: physical, mental/vital, and causal/spiritual.'
    ),
    'om so hum': (
        'oṃ so\'haṃ',
        'ॐ सोऽहम्',
        'Om [universal sound] | so [that] | ham [I am]',
        'Om — I am That. The breath mantra affirming identity of the individual self with universal consciousness.',
        'The natural breath mantra: "so" on inhalation, "ham" on exhalation, 21,600 times per day.'
    ),
    'gayatri mantra': (
        'oṃ bhūr bhuvaḥ svaḥ | tat savitur vareṇyaṃ | bhargo devasya dhīmahi | dhiyo yo naḥ pracodayāt',
        'ॐ भूर्भुवः स्वः | तत्सवितुर्वरेण्यं | भर्गो देवस्य धीमहि | धियो यो नः प्रचोदयात्',
        'Om [universal] | bhūr [earth] | bhuvaḥ [atmosphere] | svaḥ [heaven] | tat [that] | savitur [of the sun / vivifier] | vareṇyaṃ [most excellent] | bhargo [radiance] | devasya [of the divine] | dhīmahi [we meditate] | dhiyo [intellects] | yo [who] | naḥ [our] | pracodayāt [may inspire]',
        'Om. We meditate on the excellent divine radiance of Savitur (the creative sun). May that inspire our intellects.',
        'The Gāyatrī — Rigveda 3.62.10. The mother of all mantras. A prayer for illumination of the intellect.'
    ),
    'om tat sat': (
        'oṃ tat sat',
        'ॐ तत् सत्',
        'Om [universal sound] | tat [that / the absolute] | sat [being / truth / existence]',
        'Om. That is Truth. The three names of Brahman — the universal, the transcendent, and pure being.',
        'Bhagavad Gita 17.23. The triple designation of Brahman: Om (sacred sound), Tat (the transcendent), Sat (existence).'
    ),
    'aham brahmasmi': (
        'ahaṃ brahmāsmi',
        'अहं ब्रह्मास्मि',
        'aham [I] | brahma [the vast / Brahman] | asmi [I am]',
        'I am Brahman. I am the infinite, the absolute, the universal consciousness.',
        'One of the four Mahāvākyas (great sayings) from the Brihadaranyaka Upanishad. The declaration of non-dual identity.'
    ),
    'tat tvam asi': (
        'tat tvam asi',
        'तत् त्वम् असि',
        'tat [that / the absolute] | tvam [you] | asi [are]',
        'That thou art. You are That — the absolute, the universal self, Brahman.',
        'Mahāvākya from the Chandogya Upanishad. Repeated twelve times as the great teaching of non-duality.'
    ),
    'prajnanam brahma': (
        'prajñānaṃ brahma',
        'प्रज्ञानं ब्रह्म',
        'prajñānam [consciousness / pure knowing] | brahma [the vast / Brahman]',
        'Consciousness is Brahman. Pure awareness itself is the absolute.',
        'Mahāvākya from the Aitareya Upanishad (Rigveda). Identifies pure knowing with the ultimate reality.'
    ),
    'ayam atma brahma': (
        'ayam ātmā brahma',
        'अयम् आत्मा ब्रह्म',
        'ayam [this] | ātmā [the self / soul] | brahma [the vast / Brahman]',
        'This self is Brahman. The individual soul and the universal are one.',
        'Mahāvākya from the Mandukya Upanishad. The fourth great saying affirming the identity of Atman and Brahman.'
    ),
    'lokah samastah sukhino bhavantu': (
        'lokāḥ samastāḥ sukhinō bhavantu',
        'लोकाः समस्ताः सुखिनो भवन्तु',
        'lokāḥ [worlds / all beings] | samastāḥ [all / entire] | sukhino [may be happy / may experience ease] | bhavantu [may they be]',
        'May all beings in all worlds be happy and at ease.',
        'A universal prayer of loving-kindness, closing many yoga classes. Not Vedic but widely used in Sanskrit tradition.'
    ),
}

def lookup_mantra(text):
    """Check if text matches a known mantra phrase."""
    key = text.lower().strip()
    if key in MANTRA_PHRASES:
        return MANTRA_PHRASES[key]
    # Partial match
    for phrase, data in MANTRA_PHRASES.items():
        if phrase in key or key in phrase:
            return data
    return None


# ═══════════════════════════════════════════════════════════════════
#  AUDIO UTILITIES
# ═══════════════════════════════════════════════════════════════════

def play_wav(path, stop_event=None):
    """Play a WAV file using platform audio."""
    path = str(path)
    try:
        if sys.platform == 'win32':
            try:
                import winsound
                winsound.PlaySound(path, winsound.SND_FILENAME | winsound.SND_ASYNC)
                return
            except Exception:
                pass
            if shutil.which('powershell'):
                subprocess.Popen(['powershell', '-c',
                    f'(New-Object System.Media.SoundPlayer "{path}").PlaySync()'],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                return
        elif sys.platform == 'darwin':
            if shutil.which('afplay'):
                p = subprocess.Popen(['afplay', path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                if stop_event:
                    while p.poll() is None:
                        if stop_event.is_set():
                            p.terminate()
                            return
                        time.sleep(0.1)
                return
        for player, extra in [('aplay',[]),('paplay',[]),('play',[]),
                               ('ffplay',['-nodisp','-autoexit']),
                               ('mpv',['--no-video','--really-quiet'])]:
            if shutil.which(player):
                p = subprocess.Popen([player]+extra+[path],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                if stop_event:
                    while p.poll() is None:
                        if stop_event.is_set():
                            p.terminate()
                            return
                        time.sleep(0.1)
                return
    except Exception:
        pass

def read_wav_info(path):
    """Return dict with WAV metadata."""
    try:
        with wave.open(str(path), 'r') as w:
            return {
                'channels': w.getnchannels(),
                'sample_rate': w.getframerate(),
                'frames': w.getnframes(),
                'duration': w.getnframes() / w.getframerate(),
                'sample_width': w.getsampwidth(),
            }
    except Exception as e:
        return {'error': str(e)}

# ── ffmpeg: cached path so we never search PATH twice ─────────────
_FFMPEG_CACHE = {}   # {'path': str|None, 'checked': bool}

# Extra search locations beyond shutil.which — covers common manual installs
_FFMPEG_EXTRA_PATHS = {
    'win32':  [
        r'C:\ffmpeg\bin\ffmpeg.exe',
        r'C:\Program Files\ffmpeg\bin\ffmpeg.exe',
        r'C:\Program Files (x86)\ffmpeg\bin\ffmpeg.exe',
        os.path.expandvars(r'%LOCALAPPDATA%\Microsoft\WinGet\Links\ffmpeg.exe'),
        os.path.expandvars(r'%USERPROFILE%\scoop\apps\ffmpeg\current\bin\ffmpeg.exe'),
    ],
    'darwin': [
        '/usr/local/bin/ffmpeg',
        '/opt/homebrew/bin/ffmpeg',
        '/opt/local/bin/ffmpeg',
    ],
    'linux':  [
        '/usr/bin/ffmpeg',
        '/usr/local/bin/ffmpeg',
        '/snap/bin/ffmpeg',
    ],
}

def _ffmpeg_path():
    """
    Return the path to ffmpeg/avconv — cached after first successful find.
    Checks PATH first (instant), then common install locations.
    Never rescans if already found.
    """
    if _FFMPEG_CACHE.get('checked'):
        return _FFMPEG_CACHE.get('path')

    # 1. Fast PATH scan
    for tool in ['ffmpeg', 'avconv']:
        p = shutil.which(tool)
        if p:
            _FFMPEG_CACHE['path'] = p
            _FFMPEG_CACHE['checked'] = True
            return p

    # 2. Common hard-coded locations (zero subprocess overhead)
    plat = sys.platform
    key  = 'linux' if plat.startswith('linux') else plat
    for candidate in _FFMPEG_EXTRA_PATHS.get(key, []):
        if os.path.isfile(candidate):
            # Add its directory to PATH so subprocesses find it too
            os.environ['PATH'] = os.path.dirname(candidate) + os.pathsep + os.environ.get('PATH', '')
            _FFMPEG_CACHE['path'] = candidate
            _FFMPEG_CACHE['checked'] = True
            return candidate

    _FFMPEG_CACHE['path'] = None
    _FFMPEG_CACHE['checked'] = True
    return None


def _try_install_ffmpeg(status_cb=None):
    """
    Auto-install ffmpeg if missing.  Returns its path or None.
    Checks cache first — never runs install logic if already present.
    """
    def _log(msg):
        if status_cb: status_cb(msg)

    p = _ffmpeg_path()
    if p:
        return p   # ← already have it, skip everything

    _log('ffmpeg not found — attempting auto-install…')
    _FFMPEG_CACHE['checked'] = False   # reset so post-install scan picks it up

    def _recheck():
        _FFMPEG_CACHE['checked'] = False
        return _ffmpeg_path()

    # ── Linux / WSL: apt / snap ───────────────────────────────────
    if sys.platform.startswith('linux'):
        for apt in ['apt-get', 'apt']:
            if shutil.which(apt):
                for cmd in (
                    ['sudo', '-n', apt, 'install', '-y', 'ffmpeg'],  # -n = non-interactive
                    [apt, 'install', '-y', 'ffmpeg'],
                ):
                    _log(f'Trying: {" ".join(cmd)}')
                    try:
                        subprocess.run(cmd, capture_output=True, timeout=120)
                        p = _recheck()
                        if p:
                            _log(f'✓ ffmpeg installed via {apt}')
                            return p
                    except Exception as e:
                        _log(f'{apt} attempt: {e}')
                break
        if shutil.which('snap'):
            try:
                subprocess.run(['sudo', 'snap', 'install', 'ffmpeg'],
                               capture_output=True, timeout=120)
                p = _recheck()
                if p:
                    _log('✓ ffmpeg installed via snap')
                    return p
            except Exception:
                pass

    # ── macOS: brew ───────────────────────────────────────────────
    elif sys.platform == 'darwin':
        if shutil.which('brew'):
            _log('Trying: brew install ffmpeg')
            try:
                subprocess.run(['brew', 'install', 'ffmpeg'],
                               capture_output=True, timeout=300)
                p = _recheck()
                if p:
                    _log('✓ ffmpeg installed via Homebrew')
                    return p
            except Exception as e:
                _log(f'brew attempt failed: {e}')
        else:
            _log('Homebrew not found — install from https://brew.sh then: brew install ffmpeg')

    # ── Windows ───────────────────────────────────────────────────
    elif sys.platform == 'win32':
        for mgr, cmd in [
            ('winget', ['winget', 'install', '--id', 'Gyan.FFmpeg', '-e', '--silent']),
            ('choco',  ['choco', 'install', 'ffmpeg', '-y']),
            ('scoop',  ['scoop', 'install', 'ffmpeg']),
        ]:
            if shutil.which(mgr):
                _log(f'Trying: {mgr} install ffmpeg')
                try:
                    subprocess.run(cmd, capture_output=True, timeout=300)
                    # Refresh common post-install paths
                    for extra in [
                        r'C:\Program Files\ffmpeg\bin',
                        os.path.expandvars(r'%LOCALAPPDATA%\Microsoft\WinGet\Links'),
                        os.path.expandvars(r'%USERPROFILE%\scoop\apps\ffmpeg\current\bin'),
                    ]:
                        if os.path.isdir(extra):
                            os.environ['PATH'] = extra + os.pathsep + os.environ.get('PATH', '')
                    p = _recheck()
                    if p:
                        _log(f'✓ ffmpeg installed via {mgr}')
                        return p
                except Exception as e:
                    _log(f'{mgr} attempt: {e}')

    _log('Auto-install unsuccessful. WAV works without ffmpeg. '
         'Install ffmpeg manually: https://ffmpeg.org/download.html')
    return None


def mp3_to_wav(mp3_path, status_cb=None):
    """
    Decode MP3 → WAV at maximum speed.

    Speed tricks applied:
      • _ffmpeg_path() is cached — zero PATH overhead on repeat calls
      • ffmpeg flags: -threads 0 (all cores), -vn (skip video stream),
        output PCM 16-bit 44100 Hz mono (smallest WAV the analyser needs),
        -loglevel error (no log parsing overhead)
      • Streams stderr live so UI gets real-time progress dots
      • Falls back to auto-install only when truly missing
    """
    def _log(msg):
        if status_cb: status_cb(msg)

    out = tempfile.NamedTemporaryFile(suffix='.wav', delete=False)
    out.close()
    out_path = out.name

    def _run_ffmpeg(binary):
        """Run conversion; stream stderr for live progress feedback."""
        cmd = [
            binary,
            '-y',                        # overwrite output without asking
            '-threads', '0',             # use ALL available CPU cores
            '-i', str(mp3_path),
            '-vn',                       # drop any video stream instantly
            '-acodec', 'pcm_s16le',      # 16-bit PCM — direct, no re-encoding
            '-ar', '44100',              # standard sample rate
            '-ac', '1',                  # mono — halves data, enough for analysis
            '-loglevel', 'error',        # suppress non-error noise
            out_path,
        ]
        _log(f'Converting with {os.path.basename(binary)}…')
        proc = subprocess.Popen(cmd,
                                stdout=subprocess.DEVNULL,
                                stderr=subprocess.PIPE)
        # Drain stderr in a tiny loop — keeps the thread alive without blocking
        errbuf = []
        while True:
            line = proc.stderr.readline()
            if not line:
                if proc.poll() is not None:
                    break
                time.sleep(0.05)
                continue
            errbuf.append(line.decode(errors='replace').strip())

        proc.wait()
        if proc.returncode == 0 and os.path.getsize(out_path) > 44:
            return True
        if errbuf:
            _log('ffmpeg: ' + errbuf[-1])
        return False

    # ── Fast path: ffmpeg already known ───────────────────────────
    binary = _ffmpeg_path()
    if binary:
        if _run_ffmpeg(binary):
            return out_path
        _log('ffmpeg conversion failed — check file integrity.')
        return None

    # ── Slow path: need to install ────────────────────────────────
    binary = _try_install_ffmpeg(status_cb=status_cb)
    if binary:
        if _run_ffmpeg(binary):
            return out_path

    _log('Could not convert MP3. Please use a WAV file or install ffmpeg.')
    return None

# ═══════════════════════════════════════════════════════════════════
#  SYNTHESIS ENGINE LOADER
# ═══════════════════════════════════════════════════════════════════

_synth_ns = None

def get_synth_ns():
    global _synth_ns
    if _synth_ns is None:
        ns = {'__name__': 'sk_synth', '__file__': ''}
        exec(CORE, ns)
        _synth_ns = ns
    return _synth_ns


# ═══════════════════════════════════════════════════════════════════
#  PER-FRAME CHRONOLOGICAL ANALYSIS ENGINE
#  Each 0.1-second window: FFT → dominant Hz → MIDI note → HAZ →
#  Vedic/Classical Sanskrit svara → Devanagari → English meaning
# ═══════════════════════════════════════════════════════════════════

# Full MIDI note → Sanskrit/Vedic mapping
# Each entry: (midi_lo, midi_hi, svara_iast, svara_dev, svara_name, vedic_meaning, english_meaning)
MIDI_SVARA_TABLE = [
    # Sub-bass / drone territory — Vedic "cosmic hum" region
    (0,  23,  'anāhata-nāda',    'अनाहत-नाद', 'Anāhata Nāda',
     'The unstruck, uncaused sound — the primordial vibration beneath all audible sound.',
     'The cosmic hum; the silent sound of pure being.'),
    # Low bass — Mūlādhāra (root chakra) tones
    (24, 35,  'mūla-svara',      'मूल-स्वर',  'Mūla Svara',
     'Root tone — Mūlādhāra. The earth vibration, foundation, primal stability.',
     'Earth tone; the root frequency of grounded existence.'),
    # Upper bass — Svādhiṣṭhāna region
    (36, 47,  'ādhāra-svara',    'आधार-स्वर', 'Ādhāra Svara',
     'Foundation svara — Svādhiṣṭhāna. Water element, creative flow, generation.',
     'Creative-flow tone; vital waters of becoming.'),
    # Mid-range — Sa (C4 region, MIDI 60)
    (48, 51,  'Sa',              'स॒',        'Sa — Ṣaḍja',
     'Ṣaḍja — "born of six." The self-born tonic, peacock-born, earth-tone, root of all svaras.',
     'The tonic; grounding; self-luminous origin.'),
    (52, 53,  'Ri (komal)',      'रि॒',       'Ri Komal — Ṛṣabha',
     'Komal Ṛṣabha — the soft second degree. The bull-born note, fire, rising energy.',
     'Soft second; rising vitality.'),
    (54, 54,  'Ri (tīvra)',      'रि',        'Ri Tīvra — Ṛṣabha',
     'Sharp Ṛṣabha — forceful ascent, the flame leaping upward.',
     'Sharp second; forceful solar rising.'),
    (55, 56,  'Ga (komal)',      'ग॒',        'Ga Komal — Gāndhāra',
     'Komal Gāndhāra — fragrant third. The goat-born note, gandha (primordial fragrance).',
     'Soft third; fragrant presence.'),
    (57, 57,  'Ga (tīvra)',      'ग',         'Ga Tīvra — Gāndhāra',
     'Sharp Gāndhāra — vivid fragrance, heightened presence.',
     'Sharp third; vivid radiance.'),
    (58, 59,  'Ma (śuddha)',     'म',         'Ma Śuddha — Madhyama',
     'Madhyama — the middle note. The dove-born centre, equipoise, the pivot of cosmic music.',
     'Pure fourth; the still centre, balance.'),
    (60, 60,  'Ma (tīvra)',      'म॑',        'Ma Tīvra — Madhyama',
     'Tīvra Madhyama — raised fourth, the Lydian pivot, divine longing.',
     'Sharp fourth; yearning, divine aspiration.'),
    (61, 62,  'Pa',             'प',         'Pa — Pañcama',
     'Pañcama — the fifth. The cuckoo-born note, ratio 3:2, lunar harmony, natural resonance.',
     'The fifth; harmony; the moon.'),
    (63, 64,  'Dha (komal)',    'ध॒',        'Dha Komal — Dhaivata',
     'Komal Dhaivata — the soft sixth. Frog-born, Mercury, the note of rain and abundance.',
     'Soft sixth; abundance, flow.'),
    (65, 65,  'Dha (tīvra)',    'ध',         'Dha Tīvra — Dhaivata',
     'Tīvra Dhaivata — sharp sixth, heightened abundance, solar radiance.',
     'Sharp sixth; solar abundance.'),
    (66, 67,  'Ni (komal)',     'नि॒',       'Ni Komal — Niṣāda',
     'Komal Niṣāda — the soft seventh. Elephant-born, Saturn, mystic dissolution.',
     'Soft seventh; the mystic, dissolution.'),
    (68, 68,  'Ni (tīvra)',     'नि',        'Ni Tīvra — Niṣāda',
     'Tīvra Niṣāda — the leading seventh, reaching toward transcendence.',
     'Sharp seventh; transcendence, the threshold.'),
    (69, 71,  'Sa (tāra)',      'स',         'Sa Tāra — Upper Ṣaḍja',
     'Upper-octave Ṣaḍja — the return, completion, unity at a higher vibration.',
     'Upper tonic; completion, return to source.'),
    # High register — Viśuddha / Ājñā chakra tones
    (72, 83,  'tāra-svara',     'तार-स्वर',  'Tāra Svara',
     'Tāra (high) — Viśuddha/Ājñā region. Pure expression, akāśa (ether), clarity of mind.',
     'High register; ethereal clarity, throat and brow.'),
    # Very high — Sahasrāra
    (84, 95,  'ati-tāra',       'अति-तार',   'Ati-Tāra',
     'Beyond tāra — Sahasrāra. The thousand-petalled lotus, pure consciousness, light itself.',
     'Crown register; pure awareness, the luminous void.'),
    # Ultrasonic territory — formless
    (96, 127, 'para-nāda',      'पर-नाद',    'Para Nāda',
     'Para Nāda — the supreme, transcendent sound beyond hearing. The silence that contains all.',
     'Transcendent sound; the silence beyond.'),
]

# HAZ (hazard / tension level mapping) — maps spectral energy to guna/rasa
HAZ_LEVELS = [
    (0.00, 0.05, 'śānta',   'शान्त',  'Śānta rasa — tranquillity, the silent resting ground.'),
    (0.05, 0.15, 'prasāda', 'प्रसाद', 'Prasāda — grace, gentle luminosity, clarified stillness.'),
    (0.15, 0.30, 'mādhurya','माधुर्य','Mādhurya — sweetness, melodic flow, sattva in motion.'),
    (0.30, 0.50, 'vīra',    'वीर',    'Vīra rasa — heroic energy, rajas, dynamic assertion.'),
    (0.50, 0.70, 'raudra',  'रौद्र',  'Raudra rasa — fierce energy, the fire of transformation.'),
    (0.70, 0.90, 'bhayanaka','भयानक','Bhayanaka — awesome, fearful intensity, tamas-rajas.'),
    (0.90, 1.01, 'adbhuta', 'अद्भुत', 'Adbhuta — the wondrous, overwhelming, the sublime peak.'),
]

def freq_to_midi(freq):
    """Convert Hz to MIDI note number (float)."""
    if freq <= 0:
        return 0.0
    return 69.0 + 12.0 * math.log2(freq / 440.0)

def midi_to_svara(midi_note):
    """Map a MIDI note number to the closest Sanskrit svara entry."""
    midi_int = int(round(midi_note))
    midi_int = max(0, min(127, midi_int))
    for lo, hi, iast, dev, name, vedic, eng in MIDI_SVARA_TABLE:
        if lo <= midi_int <= hi:
            return iast, dev, name, vedic, eng
    return 'Sa', 'स', 'Sa', 'Ṣaḍja — the tonic.', 'The tonic note.'

def energy_to_haz(norm_energy):
    """Map normalized frame energy [0..1] to a rasa/HAZ level."""
    for lo, hi, iast, dev, desc in HAZ_LEVELS:
        if lo <= norm_energy < hi:
            return iast, dev, desc
    return HAZ_LEVELS[-1][2], HAZ_LEVELS[-1][3], HAZ_LEVELS[-1][4]

# ── Dependency bootstrap: numpy auto-install ──────────────────────
# Runs once at import time in a background thread so the GUI is never
# blocked. Sets _NP to the numpy module (or None on failure).
_NP = None
_NP_LOCK = threading.Lock()

def _bootstrap_numpy():
    """
    Try to import numpy. If missing, silently pip-install it into the
    user site-packages and try again. Called in a daemon thread at startup
    so it never blocks the GUI. Sets the module-level _NP reference.
    """
    global _NP
    try:
        import numpy as np
        with _NP_LOCK:
            _NP = np
        return
    except ImportError:
        pass

    # Not installed — try pip in a subprocess (no sudo needed for --user)
    try:
        subprocess.run(
            [sys.executable, '-m', 'pip', 'install', '--quiet',
             '--disable-pip-version-check', '--user', 'numpy'],
            capture_output=True, timeout=120
        )
        # Force Python to see newly installed user-site packages
        import importlib, site
        importlib.invalidate_caches()
        # Make sure user site-packages is on sys.path
        user_site = site.getusersitepackages()
        if user_site not in sys.path:
            sys.path.insert(0, user_site)
        import numpy as np
        with _NP_LOCK:
            _NP = np
    except Exception:
        pass  # falls through to stdlib FFT tier

# Kick off numpy bootstrap immediately in background
threading.Thread(target=_bootstrap_numpy, daemon=True, name='numpy-bootstrap').start()


# ── Tier 2: pure-stdlib Cooley-Tukey radix-2 FFT ─────────────────
# 1000× faster than the old DFT loop for N=4096.
# Only uses cmath (stdlib) — no dependencies.
import cmath as _cmath

def _stdlib_fft(x):
    """
    Iterative Cooley-Tukey radix-2 FFT (in-place) on a list of complex numbers.
    N must be a power of two.  Returns list of complex outputs.
    """
    N = len(x)
    # Bit-reversal permutation
    j = 0
    for i in range(1, N):
        bit = N >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            x[i], x[j] = x[j], x[i]
    # Butterfly stages
    length = 2
    while length <= N:
        half = length >> 1
        w_step = _cmath.exp(-2j * math.pi / length)
        for i in range(0, N, length):
            w = 1 + 0j
            for k in range(half):
                u = x[i + k]
                v = x[i + k + half] * w
                x[i + k]        = u + v
                x[i + k + half] = u - v
                w *= w_step
        length <<= 1
    return x

def _next_pow2(n):
    p = 1
    while p < n:
        p <<= 1
    return p

def _compute_fft_magnitude(seg_floats, sr):
    """
    Core FFT dispatch — tries numpy first (C speed), falls back to
    stdlib Cooley-Tukey FFT, then Goertzel as last resort.

    Returns (dominant_hz, raw_energy_in_band)
    """
    N_raw = len(seg_floats)
    if N_raw < 8:
        return 0.0, 0.0

    # ── FFT size: next power of 2, capped at 4096 ─────────────────
    N = min(_next_pow2(N_raw), 4096)
    seg = seg_floats[:N]

    # Hann window coefficients (computed once per unique N via lru_cache)
    hw = _hann_window(N)

    # Band limits (50 Hz – 5000 Hz covers all musical content)
    k_lo = max(1, int(50.0  * N / sr))
    k_hi = min(N // 2, int(5000.0 * N / sr) + 1)

    # ── TIER 1: numpy (≈1 µs per frame) ──────────────────────────
    with _NP_LOCK:
        np = _NP
    if np is not None:
        try:
            arr   = np.array(seg, dtype=np.float32) * np.array(hw, dtype=np.float32)
            spec  = np.abs(np.fft.rfft(arr, n=N)) ** 2
            band  = spec[k_lo:k_hi]
            best_k = int(np.argmax(band)) + k_lo
            energy = float(np.sum(band))
            return best_k * sr / N, energy
        except Exception:
            pass  # fall through

    # ── TIER 2: stdlib Cooley-Tukey FFT (≈10–50 µs per frame) ───
    try:
        cx = [complex(seg[i] * hw[i]) for i in range(N)]
        _stdlib_fft(cx)
        best_k    = k_lo
        best_mag  = 0.0
        energy    = 0.0
        for k in range(k_lo, k_hi):
            mag = cx[k].real**2 + cx[k].imag**2
            energy += mag
            if mag > best_mag:
                best_mag = mag
                best_k   = k
        return best_k * sr / N, energy
    except Exception:
        pass  # fall through

    # ── TIER 3: Goertzel per-bin (pure math, slower but always works) ─
    # Only evaluate the bins we actually need — O(k_range × N) not O(N²)
    fw = [seg[i] * hw[i] for i in range(N)]
    best_k   = k_lo
    best_mag = 0.0
    energy   = 0.0
    TAU_N    = 2 * math.pi / N
    for k in range(k_lo, k_hi):
        coeff = 2.0 * math.cos(TAU_N * k)
        s0 = s1 = s2 = 0.0
        for samp in fw:
            s0 = samp + coeff * s1 - s2
            s2 = s1
            s1 = s0
        mag = s1*s1 + s2*s2 - s1*s2*coeff
        energy += mag
        if mag > best_mag:
            best_mag = mag
            best_k   = k
    return best_k * sr / N, energy


# Hann window cache — reuse across all frames of the same size
_HANN_CACHE = {}
def _hann_window(N):
    if N not in _HANN_CACHE:
        _HANN_CACHE[N] = [0.5 - 0.5 * math.cos(2 * math.pi * i / (N - 1))
                          for i in range(N)]
    return _HANN_CACHE[N]


def analyse_audio_frames(wav_path, frame_sec=0.1, progress_cb=None):
    """
    Analyse a WAV file in frame_sec-wide windows at maximum speed.

    Speed tiers (auto-selected):
      • numpy  : ~0.5 ms total for a 6-min file  (if available)
      • stdlib FFT: ~5–15 s for a 6-min file
      • Goertzel  : ~60–120 s for a 6-min file (last resort)

    Returns list of dicts, one per 0.1 s frame, chronological order.
    Each dict keys: t_start, t_end, dom_hz, midi, midi_int, midi_name,
                    svara_iast, svara_dev, svara_name, vedic, english,
                    haz_iast, haz_dev, haz_desc, norm_energy
    """
    MIDI_NAMES = ['C','C#','D','D#','E','F','F#','G','G#','A','A#','B']

    # ── Read WAV header ───────────────────────────────────────────
    with wave.open(wav_path, 'r') as wf:
        sr    = wf.getframerate()
        sw    = wf.getsampwidth()
        ch    = wf.getnchannels()
        total = wf.getnframes()

    fmt    = {1: 'b', 2: 'h', 4: 'i'}.get(sw, 'h')
    frame_n  = int(sr * frame_sec)
    n_frames = total // frame_n

    # ── Read ALL samples in one shot (no per-frame I/O) ──────────
    with wave.open(wav_path, 'r') as wf:
        raw = wf.readframes(total)
    all_samps = array.array(fmt, raw)
    if ch == 2:
        all_samps = all_samps[::2]   # downmix to mono (left channel)

    # ── Global peak for normalisation ────────────────────────────
    # numpy path is ~1000× faster for this
    with _NP_LOCK:
        np = _NP
    if np is not None:
        arr_all = np.array(all_samps, dtype=np.float32)
        global_max = float(np.max(np.abs(arr_all))) or 1.0
        # Pre-normalise entire buffer once
        norm_all = (arr_all / global_max).tolist()
    else:
        global_max = max((abs(x) for x in all_samps), default=1) or 1
        norm_all = [x / global_max for x in all_samps]

    results     = []
    raw_energies = []

    for fi in range(n_frames):
        t_start = fi * frame_sec
        t_end   = t_start + frame_sec
        lo = fi * frame_n
        hi = lo + frame_n
        seg = norm_all[lo:hi]

        if len(seg) < 8:
            raw_energies.append(0.0)
            continue

        dom_hz, raw_energy = _compute_fft_magnitude(seg, sr)
        raw_energies.append(raw_energy)

        midi_f   = freq_to_midi(dom_hz)
        midi_int = max(0, min(127, int(round(midi_f))))
        midi_name = f'{MIDI_NAMES[midi_int % 12]}{midi_int // 12 - 1}'
        s_iast, s_dev, s_name, vedic, english = midi_to_svara(midi_f)

        results.append({
            't_start'   : t_start,
            't_end'     : t_end,
            'dom_hz'    : dom_hz,
            'midi'      : midi_f,
            'midi_int'  : midi_int,
            'midi_name' : midi_name,
            'svara_iast': s_iast,
            'svara_dev' : s_dev,
            'svara_name': s_name,
            'vedic'     : vedic,
            'english'   : english,
            'raw_energy': raw_energy,
        })

        if progress_cb and fi % 20 == 0:
            progress_cb(fi, n_frames)

    # ── Post-normalise energy → HAZ/rasa ─────────────────────────
    if results:
        max_e = max(r['raw_energy'] for r in results) or 1.0
        for r in results:
            ne = r['raw_energy'] / max_e
            r['norm_energy'] = ne
            h_iast, h_dev, h_desc = energy_to_haz(ne)
            r['haz_iast'] = h_iast
            r['haz_dev']  = h_dev
            r['haz_desc'] = h_desc
            del r['raw_energy']

    if progress_cb:
        progress_cb(n_frames, n_frames)

    return results


# ═══════════════════════════════════════════════════════════════════
#  GUI
# ═══════════════════════════════════════════════════════════════════

BG      = '#07070f'
BG2     = '#0e0e1c'
BG3     = '#12122a'
PANEL   = '#0b0b18'
ACC     = '#c8a86b'   # saffron-gold
ACC2    = '#e8c88b'   # light gold
TEAL    = '#00d4aa'
RED     = '#ff4466'
DIM     = '#2a2a44'
MUTED   = '#606075'
BRIGHT  = '#e0d8c8'
SEP     = '#1a1a2e'
ORANGE  = '#e08040'
PINK    = '#c070a0'

FONT_MAIN  = ('Georgia', 11)
FONT_MONO  = ('Courier', 9)
FONT_TITLE = ('Georgia', 13, 'bold')
FONT_LABEL = ('Courier', 8, 'bold')
FONT_DEV   = ('Noto Sans Devanagari', 14) if sys.platform != 'win32' else ('Arial Unicode MS', 14)

class TooltipLabel(tk.Label):
    def __init__(self, parent, tooltip='', **kw):
        super().__init__(parent, **kw)
        self._tip = tooltip
        self.bind('<Enter>', self._show)
        self.bind('<Leave>', self._hide)
        self._tipwin = None
    def _show(self, _):
        if not self._tip: return
        x = self.winfo_rootx() + 20
        y = self.winfo_rooty() + self.winfo_height()
        self._tipwin = tw = tk.Toplevel(self)
        tw.wm_overrideredirect(True)
        tw.wm_geometry(f'+{x}+{y}')
        tk.Label(tw, text=self._tip, justify='left',
                 bg='#2a2a44', fg=BRIGHT, font=('Courier', 8),
                 relief='solid', bd=1, padx=6, pady=3).pack()
    def _hide(self, _):
        if self._tipwin:
            self._tipwin.destroy()
            self._tipwin = None

class App:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title('Sanskrit Audio Translator')
        self.root.configure(bg=BG)
        self.root.geometry('820x680')
        self.root.minsize(680, 540)

        self._loaded_path = None
        self._loaded_wav  = None   # path to usable WAV (may be converted)
        self._tmp_dir = tempfile.mkdtemp(prefix='sk_trans_')
        self._stop_ev = threading.Event()
        self._tone_path = None
        self._playing = False

        self._build_ui()

    # ─── UI BUILD ────────────────────────────────────────────────

    def _build_ui(self):
        # Title bar
        tb = tk.Frame(self.root, bg=BG2, pady=6)
        tb.pack(fill=tk.X)
        tk.Label(tb, text='✦  SANSKRIT  AUDIO  TRANSLATOR  ✦',
                 font=FONT_TITLE, fg=ACC, bg=BG2).pack()
        tk.Label(tb, text='mp3 · wav  →  literal & english  |  english  →  sanskrit  |  sound synthesis',
                 font=('Courier', 7), fg=MUTED, bg=BG2).pack(pady=(0, 2))
        tk.Frame(self.root, bg=SEP, height=1).pack(fill=tk.X)

        # Notebook
        style = ttk.Style()
        style.theme_use('default')
        style.configure('TNotebook', background=BG, borderwidth=0)
        style.configure('TNotebook.Tab', background=BG3, foreground=MUTED,
                        font=('Courier', 8, 'bold'), padding=[10, 4])
        style.map('TNotebook.Tab', background=[('selected', PANEL)],
                  foreground=[('selected', ACC)])

        nb = ttk.Notebook(self.root)
        nb.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)

        t1 = tk.Frame(nb, bg=BG); nb.add(t1, text='  ♪  AUDIO → SANSKRIT  ')
        t2 = tk.Frame(nb, bg=BG); nb.add(t2, text='  ✦  SANSKRIT → ENGLISH  ')
        t3 = tk.Frame(nb, bg=BG); nb.add(t3, text='  ↩  ENGLISH → SANSKRIT  ')
        t4 = tk.Frame(nb, bg=BG); nb.add(t4, text='  ○  TONE GENERATOR  ')
        t5 = tk.Frame(nb, bg=BG); nb.add(t5, text='  ⏱  CHRONOLOGICAL TIMELINE  ')

        self._build_audio_tab(t1)
        self._build_sk_to_en_tab(t2)
        self._build_en_to_sk_tab(t3)
        self._build_tone_tab(t4)
        self._build_timeline_tab(t5)
        self._nb = nb

        # Status bar
        self._status = tk.StringVar(value='Ready.')
        sb = tk.Frame(self.root, bg=BG2, pady=3)
        sb.pack(fill=tk.X, side=tk.BOTTOM)
        tk.Label(sb, textvariable=self._status, font=('Courier', 7),
                 fg=TEAL, bg=BG2, anchor='w').pack(side=tk.LEFT, padx=8)

    # ── TAB 1: Audio → Sanskrit ───────────────────────────────────

    def _build_audio_tab(self, parent):
        # Top: file loader
        top = tk.Frame(parent, bg=BG, pady=6, padx=8)
        top.pack(fill=tk.X)

        self._sec('FILE', top)
        row = tk.Frame(top, bg=BG)
        row.pack(fill=tk.X, pady=4)

        tk.Button(row, text='Open MP3 / WAV', font=FONT_LABEL, fg=ACC, bg=BG3,
                  relief='flat', bd=0, padx=10, pady=4, cursor='hand2',
                  activebackground=DIM, activeforeground=ACC2,
                  command=self._browse_audio).pack(side=tk.LEFT, padx=(0,8))

        self._file_lbl = tk.Label(row, text='No file loaded', font=FONT_MONO,
                                   fg=MUTED, bg=BG, anchor='w')
        self._file_lbl.pack(side=tk.LEFT, fill=tk.X, expand=True)

        # Audio info
        self._info_lbl = tk.Label(top, text='', font=FONT_MONO, fg=MUTED, bg=BG, anchor='w')
        self._info_lbl.pack(fill=tk.X, pady=2)

        # Play / Analyse
        btn_row = tk.Frame(top, bg=BG)
        btn_row.pack(fill=tk.X, pady=4)

        tk.Button(btn_row, text='▶  Play', font=FONT_LABEL, fg=TEAL, bg=BG3,
                  relief='flat', bd=0, padx=8, pady=3, cursor='hand2',
                  activebackground=DIM,
                  command=self._play_loaded).pack(side=tk.LEFT, padx=(0,6))

        tk.Button(btn_row, text='⬛  Stop', font=FONT_LABEL, fg=RED, bg=BG3,
                  relief='flat', bd=0, padx=8, pady=3, cursor='hand2',
                  activebackground=DIM,
                  command=self._stop_play).pack(side=tk.LEFT, padx=(0,12))

        tk.Button(btn_row, text='✦  Analyse & Translate Audio', font=FONT_LABEL,
                  fg=ACC2, bg=BG3, relief='flat', bd=0, padx=10, pady=3,
                  cursor='hand2', activebackground=DIM,
                  command=self._analyse_audio).pack(side=tk.LEFT)

        tk.Frame(parent, bg=SEP, height=1).pack(fill=tk.X, padx=8)

        # Results area
        res = tk.Frame(parent, bg=BG, padx=8, pady=4)
        res.pack(fill=tk.BOTH, expand=True)

        self._sec('DEVANAGARI  (LITERAL)', res)
        self._dev_out = self._text_area(res, height=3, fg=ACC)
        self._sec('WORD-BY-WORD  LITERAL  TRANSLATION', res)
        self._lit_out = self._text_area(res, height=4)
        self._sec('ENGLISH  TRANSLATION', res)
        self._en_out  = self._text_area(res, height=4, fg=BRIGHT)

    # ── TAB 2: Sanskrit → English ─────────────────────────────────

    def _build_sk_to_en_tab(self, parent):
        top = tk.Frame(parent, bg=BG, padx=8, pady=8)
        top.pack(fill=tk.X)

        self._sec('ENTER  SANSKRIT  (IAST  ROMANIZATION  OR  MANTRA  NAME)', top)
        hint = ('Type romanized Sanskrit or IAST text, e.g.:\n'
                '"om namah shivaya"  |  "om tat sat"  |  "gayatri mantra"\n'
                '"yoga dharma karma"  |  "om so hum"  |  "aham brahmasmi"')
        tk.Label(top, text=hint, font=('Courier', 7), fg=MUTED, bg=BG,
                 justify='left').pack(anchor='w', pady=(0,4))

        self._sk_in = tk.Text(top, height=3, font=FONT_MAIN,
                               fg=ACC2, bg=BG3, insertbackground=ACC,
                               relief='flat', bd=0, padx=6, pady=4)
        self._sk_in.pack(fill=tk.X)

        btn_row = tk.Frame(top, bg=BG, pady=4)
        btn_row.pack(fill=tk.X)
        tk.Button(btn_row, text='✦  Translate Sanskrit → English',
                  font=FONT_LABEL, fg=ACC, bg=BG3, relief='flat',
                  bd=0, padx=10, pady=4, cursor='hand2', activebackground=DIM,
                  command=self._translate_sk_en).pack(side=tk.LEFT)
        tk.Button(btn_row, text='Clear', font=FONT_LABEL, fg=MUTED, bg=BG3,
                  relief='flat', bd=0, padx=6, pady=4, cursor='hand2',
                  activebackground=DIM,
                  command=lambda: [self._sk_in.delete('1.0', tk.END),
                                   self._clear_sk_results()]).pack(side=tk.LEFT, padx=6)

        tk.Frame(parent, bg=SEP, height=1).pack(fill=tk.X, padx=8)
        res = tk.Frame(parent, bg=BG, padx=8, pady=4)
        res.pack(fill=tk.BOTH, expand=True)

        self._sec('DEVANAGARI', res)
        self._sk_dev = self._text_area(res, height=2, fg=ACC)
        self._sec('IAST  ROMANIZATION', res)
        self._sk_iast = self._text_area(res, height=2, fg=ORANGE)
        self._sec('WORD-BY-WORD  LITERAL', res)
        self._sk_lit  = self._text_area(res, height=4)
        self._sec('ENGLISH  MEANING', res)
        self._sk_en   = self._text_area(res, height=4, fg=BRIGHT)
        self._sec('NOTES', res)
        self._sk_note = self._text_area(res, height=2, fg=PINK)

    # ── TAB 3: English → Sanskrit ─────────────────────────────────

    def _build_en_to_sk_tab(self, parent):
        top = tk.Frame(parent, bg=BG, padx=8, pady=8)
        top.pack(fill=tk.X)

        self._sec('ENTER  ENGLISH  TEXT', top)
        hint = 'e.g.: "peace love truth" | "consciousness bliss" | "I am that" | "om"'
        tk.Label(top, text=hint, font=('Courier', 7), fg=MUTED, bg=BG,
                 justify='left').pack(anchor='w', pady=(0,4))

        self._en_in = tk.Text(top, height=3, font=FONT_MAIN,
                               fg=BRIGHT, bg=BG3, insertbackground=ACC,
                               relief='flat', bd=0, padx=6, pady=4)
        self._en_in.pack(fill=tk.X)

        btn_row = tk.Frame(top, bg=BG, pady=4)
        btn_row.pack(fill=tk.X)
        tk.Button(btn_row, text='✦  Translate English → Sanskrit',
                  font=FONT_LABEL, fg=ACC, bg=BG3, relief='flat',
                  bd=0, padx=10, pady=4, cursor='hand2', activebackground=DIM,
                  command=self._translate_en_sk).pack(side=tk.LEFT)
        tk.Button(btn_row, text='Clear', font=FONT_LABEL, fg=MUTED, bg=BG3,
                  relief='flat', bd=0, padx=6, pady=4, cursor='hand2',
                  activebackground=DIM,
                  command=lambda: [self._en_in.delete('1.0', tk.END),
                                   self._clear_en_results()]).pack(side=tk.LEFT, padx=6)

        tk.Frame(parent, bg=SEP, height=1).pack(fill=tk.X, padx=8)
        res = tk.Frame(parent, bg=BG, padx=8, pady=4)
        res.pack(fill=tk.BOTH, expand=True)

        self._sec('SANSKRIT  IAST  (ROMANIZED)', res)
        self._en_iast = self._text_area(res, height=2, fg=ORANGE)
        self._sec('DEVANAGARI', res)
        self._en_dev  = self._text_area(res, height=3, fg=ACC)
        self._sec('NOTES  /  CONTEXT', res)
        self._en_note = self._text_area(res, height=4, fg=PINK)

    # ── TAB 4: Tone Generator ─────────────────────────────────────

    def _build_tone_tab(self, parent):
        top = tk.Frame(parent, bg=BG, padx=10, pady=8)
        top.pack(fill=tk.X)

        self._sec('MANTRA  TONE  SYNTHESIS', top)
        tk.Label(top,
                 text=('Generate Sanskrit-inspired tones using the embedded synthesis engine.\n'
                       'These tones model the harmonic resonance of Vedic chanting and singing bowls.'),
                 font=('Courier', 7), fg=MUTED, bg=BG, justify='left').pack(anchor='w', pady=(0,6))

        # Preset tones row
        self._sec('PRESETS', top)
        presets = tk.Frame(top, bg=BG)
        presets.pack(fill=tk.X, pady=4)

        tones = [
            ('OM  (136 Hz)', 136.0, 'bowl'),
            ('SA  (240 Hz)', 240.0, 'bowl'),
            ('MA  (360 Hz)', 360.0, 'bowl'),
            ('GA  (432 Hz)', 432.0, 'bowl'),
            ('PA  (540 Hz)', 540.0, 'bowl'),
            ('NI  (720 Hz)', 720.0, 'bowl'),
        ]
        for label, freq, ttype in tones:
            tk.Button(presets, text=label, font=('Courier', 8, 'bold'),
                      fg=ACC, bg=BG3, relief='flat', bd=0, padx=7, pady=5,
                      cursor='hand2', activebackground=DIM, activeforeground=ACC2,
                      command=lambda f=freq, t=ttype: self._gen_tone(f, t)
                      ).pack(side=tk.LEFT, padx=3)

        # Custom tone
        self._sec('CUSTOM  TONE', top)
        cust = tk.Frame(top, bg=BG)
        cust.pack(fill=tk.X, pady=4)

        tk.Label(cust, text='Frequency (Hz):', font=FONT_LABEL, fg=MUTED, bg=BG).pack(side=tk.LEFT, padx=(0,4))
        self._freq_var = tk.StringVar(value='432')
        tk.Entry(cust, textvariable=self._freq_var, width=7, font=FONT_MAIN,
                 fg=BRIGHT, bg=BG3, insertbackground=ACC, relief='flat', bd=1).pack(side=tk.LEFT, padx=(0,10))

        tk.Label(cust, text='Duration (s):', font=FONT_LABEL, fg=MUTED, bg=BG).pack(side=tk.LEFT, padx=(0,4))
        self._dur_var = tk.StringVar(value='5')
        tk.Entry(cust, textvariable=self._dur_var, width=5, font=FONT_MAIN,
                 fg=BRIGHT, bg=BG3, insertbackground=ACC, relief='flat', bd=1).pack(side=tk.LEFT, padx=(0,10))

        tk.Label(cust, text='Type:', font=FONT_LABEL, fg=MUTED, bg=BG).pack(side=tk.LEFT, padx=(0,4))
        self._tone_type = ttk.Combobox(cust, values=['bowl','mantra_seq'], width=12,
                                        state='readonly', font=FONT_MONO)
        self._tone_type.set('bowl')
        self._tone_type.pack(side=tk.LEFT, padx=(0,10))

        tk.Button(cust, text='▶  Generate & Play', font=FONT_LABEL, fg=TEAL, bg=BG3,
                  relief='flat', bd=0, padx=10, pady=3, cursor='hand2',
                  activebackground=DIM,
                  command=self._gen_custom_tone).pack(side=tk.LEFT, padx=(0,6))

        tk.Button(cust, text='⬛  Stop', font=FONT_LABEL, fg=RED, bg=BG3,
                  relief='flat', bd=0, padx=8, pady=3, cursor='hand2',
                  activebackground=DIM,
                  command=self._stop_play).pack(side=tk.LEFT)

        # Mantra sequence
        self._sec('MANTRA  SYLLABLE  SEQUENCE', top)
        seq_f = tk.Frame(top, bg=BG)
        seq_f.pack(fill=tk.X, pady=4)
        tk.Label(seq_f, text='Syllable freqs (Hz, comma-sep):', font=FONT_LABEL, fg=MUTED, bg=BG).pack(side=tk.LEFT, padx=(0,6))
        self._seq_var = tk.StringVar(value='240,270,300,360,270,240')
        tk.Entry(seq_f, textvariable=self._seq_var, width=32, font=FONT_MONO,
                 fg=BRIGHT, bg=BG3, insertbackground=ACC, relief='flat', bd=1).pack(side=tk.LEFT, padx=(0,8))
        tk.Button(seq_f, text='▶  Play Sequence', font=FONT_LABEL, fg=TEAL, bg=BG3,
                  relief='flat', bd=0, padx=8, pady=3, cursor='hand2',
                  activebackground=DIM,
                  command=self._gen_mantra_seq).pack(side=tk.LEFT)

        # Output log
        tk.Frame(parent, bg=SEP, height=1).pack(fill=tk.X, padx=8)
        log_f = tk.Frame(parent, bg=BG, padx=8, pady=4)
        log_f.pack(fill=tk.BOTH, expand=True)
        self._sec('LOG', log_f)
        self._tone_log = scrolledtext.ScrolledText(log_f, height=8, font=FONT_MONO,
                                                    fg=TEAL, bg=BG3, relief='flat',
                                                    bd=0, state=tk.DISABLED)
        self._tone_log.pack(fill=tk.BOTH, expand=True)

    # ─── HELPERS ─────────────────────────────────────────────────

    def _sec(self, text, parent):
        f = tk.Frame(parent, bg=BG)
        f.pack(fill=tk.X, pady=(4, 1))
        tk.Label(f, text=text, font=FONT_LABEL, fg=ACC2, bg=BG).pack(side=tk.LEFT)
        tk.Frame(f, bg=DIM, height=1).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(8,0), pady=5)

    def _text_area(self, parent, height=3, fg=None):
        t = scrolledtext.ScrolledText(parent, height=height, font=FONT_MONO,
                                       fg=fg or MUTED, bg=BG3, insertbackground=ACC,
                                       relief='flat', bd=0, padx=6, pady=4,
                                       state=tk.DISABLED, wrap=tk.WORD)
        t.pack(fill=tk.X, pady=2)
        return t

    def _set_text(self, widget, text):
        widget.config(state=tk.NORMAL)
        widget.delete('1.0', tk.END)
        widget.insert(tk.END, text)
        widget.config(state=tk.DISABLED)

    def _status_set(self, msg):
        self.root.after(0, lambda: self._status.set(msg))

    def _log(self, msg):
        def _do():
            self._tone_log.config(state=tk.NORMAL)
            self._tone_log.insert(tk.END, msg + '\n')
            self._tone_log.see(tk.END)
            self._tone_log.config(state=tk.DISABLED)
        self.root.after(0, _do)

    # ─── AUDIO TAB ACTIONS ───────────────────────────────────────

    def _browse_audio(self):
        path = filedialog.askopenfilename(
            title='Open Audio File',
            filetypes=[('Audio Files', '*.wav *.mp3'), ('WAV', '*.wav'), ('MP3', '*.mp3'), ('All', '*.*')]
        )
        if not path:
            return
        self._loaded_path = path
        name = Path(path).name
        self._file_lbl.config(text=name, fg=BRIGHT)
        self._status_set(f'Loaded: {name}')

        # If MP3, kick off threaded convert (auto-installs ffmpeg if missing)
        if path.lower().endswith('.mp3'):
            self._info_lbl.config(text='Converting MP3 — checking for ffmpeg…', fg=MUTED)
            self.root.update_idletasks()
            threading.Thread(target=self._mp3_convert_thread, args=(path,), daemon=True).start()
        else:
            self._loaded_wav = path
            info = read_wav_info(path)
            if 'error' not in info:
                self._info_lbl.config(
                    text=f'WAV  |  {info["duration"]:.1f}s  |  {info["sample_rate"]} Hz  |  '
                         f'{info["channels"]}ch  |  {info["sample_width"]*8}-bit',
                    fg=TEAL)
            else:
                self._info_lbl.config(text=f'Error reading file: {info["error"]}', fg=RED)


    def _mp3_convert_thread(self, path):
        """
        Background thread: convert MP3 → WAV, auto-installing ffmpeg if needed.
        Updates the info label with progress so the UI stays responsive.
        """
        def _status(msg):
            self.root.after(0, lambda m=msg: (
                self._info_lbl.config(text=m, fg=ORANGE),
                self._status.set(m),
            ))

        _status('Checking for ffmpeg…')

        # status_cb feeds progress back to the UI label while install runs
        wav = mp3_to_wav(path, status_cb=_status)

        if wav:
            info = read_wav_info(wav)
            self._loaded_wav = wav
            self.root.after(0, lambda: self._info_lbl.config(
                text=f'MP3 → WAV  |  {info.get("duration",0):.1f}s  |  '
                     f'{info.get("sample_rate",0)} Hz  |  {info.get("channels",0)}ch',
                fg=TEAL))
            self._status_set('MP3 loaded and converted.')
        else:
            self._loaded_wav = None
            self.root.after(0, lambda: self._info_lbl.config(
                text='ffmpeg unavailable — WAV spectral analysis disabled. '
                     'Text translation still works. Install ffmpeg from ffmpeg.org.',
                fg=ORANGE))
            self._status_set('MP3: ffmpeg not available.')

    def _play_loaded(self):
        if not self._loaded_wav:
            messagebox.showinfo('No File', 'Please load a WAV or MP3 file first.')
            return
        self._stop_ev.clear()
        self._playing = True
        self._status_set('Playing...')
        threading.Thread(target=self._play_thread, args=(self._loaded_wav,), daemon=True).start()

    def _play_thread(self, path):
        play_wav(path, self._stop_ev)
        self._playing = False
        self._status_set('Playback finished.')

    def _stop_play(self):
        self._stop_ev.set()
        self._playing = False
        self._status_set('Stopped.')

    def _analyse_audio(self):
        """
        Analyse the loaded audio file.
        1. Summary analysis for Tab 1 (dominant freq of full file).
        2. Also triggers the chronological 0.1s frame timeline on Tab 5.
        """
        if not self._loaded_path:
            messagebox.showinfo('No File', 'Please load an audio file first.')
            return
        self._status_set('Analysing...')
        threading.Thread(target=self._analyse_thread, daemon=True).start()

    def _analyse_thread(self):
        try:
            path = self._loaded_wav or self._loaded_path

            # Read WAV samples for FFT analysis
            dev_text = ''
            lit_text = ''
            en_text  = ''

            if path and path.endswith('.wav'):
                info = read_wav_info(path)
                if 'error' not in info:
                    # Read first ~0.5s for FFT
                    with wave.open(path, 'r') as wf:
                        sr = wf.getframerate()
                        sw = wf.getsampwidth()
                        ch = wf.getnchannels()
                        n_read = min(int(sr * 0.5), wf.getnframes())
                        raw = wf.readframes(n_read)

                    # Convert to mono float samples
                    fmt = {1: 'b', 2: 'h', 4: 'i'}.get(sw, 'h')
                    samps = array.array(fmt, raw)
                    if ch == 2:
                        samps = samps[::2]  # take left channel
                    if len(samps) == 0:
                        raise ValueError('No audio samples found')

                    # Normalize
                    maxv = max(abs(x) for x in samps) or 1
                    fsamps = [x / maxv for x in samps]

                    # Simple DFT on first 2048 samples
                    N = min(2048, len(fsamps))
                    fsamps = fsamps[:N]
                    # Compute FFT magnitudes (real DFT via stdlib math)
                    mags = []
                    freqs = []
                    for k in range(1, N//2):
                        re = sum(fsamps[n] * math.cos(2*math.pi*k*n/N) for n in range(N))
                        im = sum(fsamps[n] * math.sin(2*math.pi*k*n/N) for n in range(N))
                        mags.append(re*re + im*im)
                        freqs.append(k * sr / N)

                    # Find dominant frequency
                    if mags:
                        dom_idx = max(range(len(mags)), key=lambda i: mags[i])
                        dom_freq = freqs[dom_idx]
                    else:
                        dom_freq = 440.0

                    # Map to nearest Sanskrit solfege (Sa-Ri-Ga-Ma-Pa-Dha-Ni)
                    # Base: Sa=240, Ri=270, Ga=300, Ma=360, Pa=480, Dha=540, Ni=600
                    SVARA_MAP = [
                        (136, 'oṃ / Sa̱ (Shadja)', 'ॐ', 'The primal root tone — the ground of all sound; equivalent to the first note Sa in Indian classical music.'),
                        (240, 'Sa (Shadja)', 'स', 'Shadja — the self-born note, the tonic, the foundation. Associated with the peacock, the earth, the ground of being.'),
                        (270, 'Ri (Rishabha)', 'रि', 'Rishabha — the bull note, the second degree. Associated with the chataka bird and the element of fire.'),
                        (300, 'Ga (Gandhara)', 'ग', 'Gandhara — the third note, associated with the goat, the pure gandha (fragrance of existence).'),
                        (360, 'Ma (Madhyama)', 'म', 'Madhyama — the middle note, the fourth degree. The dove, the midpoint, balance and equipoise.'),
                        (432, 'Tuning A=432', 'अ', 'The 432 Hz tuning — considered by many traditions to align with natural cosmic resonance.'),
                        (480, 'Pa (Panchama)', 'प', 'Panchama — the fifth, generated by the ratio 3:2. The kokila (cuckoo), the moon, pure harmony.'),
                        (528, 'Solfeggio MI', 'मि', '528 Hz — the "miracle tone" said to relate to DNA repair and transformation in some traditions.'),
                        (540, 'Dha (Dhaivata)', 'ध', 'Dhaivata — the sixth note, the frog, the planet Mercury, the note of rain and abundance.'),
                        (600, 'Ni (Nishada)', 'नि', 'Nishada — the seventh note, the elephant, Saturn, the note of the mystic and the dissolving.'),
                        (720, 'Sa (upper octave)', 'स॒', 'The octave return of Shadja — completion of the cycle, unity restored at a higher vibration.'),
                    ]

                    best = min(SVARA_MAP, key=lambda x: abs(x[0] - dom_freq))
                    svara_name, svara_dev, svara_desc = best[1], best[2], best[3]

                    dur = info['duration']
                    dur_desc = 'short' if dur < 5 else 'medium' if dur < 30 else 'long'

                    # Build outputs
                    dev_text = (f'{svara_dev}\n\nDominant frequency: {dom_freq:.1f} Hz\n'
                                f'Nearest Sanskrit svara: {svara_name}')

                    lit_text = (
                        f'Audio duration: {dur:.2f}s ({dur_desc})\n'
                        f'Sample rate: {info["sample_rate"]} Hz  |  Channels: {info["channels"]}\n'
                        f'Dominant frequency: {dom_freq:.1f} Hz\n\n'
                        f'Sanskrit svara (note): {svara_name}\n'
                        f'Devanagari: {svara_dev}\n\n'
                        f'Literal meaning of svara:\n{svara_desc}'
                    )

                    en_text = (
                        f'This audio resonates most strongly at {dom_freq:.1f} Hz, '
                        f'corresponding to the Sanskrit note {svara_name}.\n\n'
                        f'{svara_desc}\n\n'
                        f'In Sanskrit music theory (Natyashastra), the seven svaras (Sa Ri Ga Ma Pa Dha Ni) '
                        f'are considered the living vibrations of cosmic consciousness. Each svara is said to '
                        f'originate from the breath of a different animal and correspond to one of the seven '
                        f'chakras, seven planets, and seven emotional states (rasas).\n\n'
                        f'The word "svara" (स्वर) means "one\'s own" (sva) + "ray of light/sound" (ra) — '
                        f'a self-luminous tone that arises from within.'
                    )
                else:
                    raise ValueError(info['error'])
            else:
                # No WAV available (MP3 without ffmpeg)
                name = Path(self._loaded_path).name
                dev_text = 'ॐ'
                lit_text = (f'File: {name}\n\nNote: Full frequency analysis requires WAV format or ffmpeg for MP3 conversion.\n\n'
                            f'The file has been loaded. Textual Sanskrit translation is available via the\n'
                            f'"Sanskrit → English" tab if you enter the mantra text manually.')
                en_text  = ('To translate audio content:\n'
                            '• WAV files: full spectral analysis performed\n'
                            '• MP3 files: requires ffmpeg (install from ffmpeg.org) for conversion\n\n'
                            'You can also use the "Sanskrit → English" tab to translate any Sanskrit text directly.')

            self.root.after(0, lambda: (
                self._set_text(self._dev_out, dev_text),
                self._set_text(self._lit_out, lit_text),
                self._set_text(self._en_out, en_text),
                self._status_set('Analysis complete. Running 0.1s timeline…'),
            ))

            # Also kick off the chronological timeline automatically
            if path and path.endswith('.wav'):
                self.root.after(100, self._start_timeline_analysis)

        except Exception as e:
            self.root.after(0, lambda: (
                self._set_text(self._lit_out, f'Analysis error: {e}'),
                self._status_set(f'Error: {e}'),
            ))

    # ── TAB 5: Chronological Timeline ────────────────────────────

    # ── Timeline constants ────────────────────────────────────────
    _TL_ROW_H   = 16   # pixels per row
    _TL_FONT    = ('Courier', 8)
    _TL_FONT_B  = ('Courier', 8, 'bold')
    # Column x-positions (pixels from left)
    _TL_COL = {
        'bar':    2,
        'time':  68,
        'hz':   128,
        'midi': 188,
        'haz':  228,
        'dev':  368,
        'iast': 418,
        'eng':  568,
    }

    def _build_timeline_tab(self, parent):
        top = tk.Frame(parent, bg=BG, padx=8, pady=6)
        top.pack(fill=tk.X)

        self._sec('CHRONOLOGICAL  0.1-SECOND  MIDI → HAZ → SANSKRIT → ENGLISH  TIMELINE', top)
        hint = ('Load a WAV/MP3 on the AUDIO tab, then click  ▶ Run Timeline Analysis.\n'
                'Each 0.1-second frame: Hz → MIDI → HAZ/rasa → Vedic svara → Devanagari → English.\n'
                'Scroll with mouse wheel. All frames rendered instantly after analysis.')
        tk.Label(top, text=hint, font=('Courier', 7), fg=MUTED, bg=BG,
                 justify='left').pack(anchor='w', pady=(0, 4))

        btn_row = tk.Frame(top, bg=BG)
        btn_row.pack(fill=tk.X, pady=4)

        self._tl_btn = tk.Button(btn_row, text='▶  Run Timeline Analysis (0.1 s frames)',
                  font=FONT_LABEL, fg=ACC2, bg=BG3, relief='flat',
                  bd=0, padx=10, pady=4, cursor='hand2', activebackground=DIM,
                  command=self._start_timeline_analysis)
        self._tl_btn.pack(side=tk.LEFT, padx=(0, 8))

        tk.Button(btn_row, text='Clear', font=FONT_LABEL, fg=MUTED, bg=BG3,
                  relief='flat', bd=0, padx=6, pady=4, cursor='hand2',
                  activebackground=DIM,
                  command=self._clear_timeline).pack(side=tk.LEFT)

        self._tl_progress = tk.Label(btn_row, text='', font=('Courier', 7),
                                     fg=TEAL, bg=BG, anchor='w')
        self._tl_progress.pack(side=tk.LEFT, padx=10)

        tk.Frame(parent, bg=SEP, height=1).pack(fill=tk.X, padx=8)

        # Fixed column-header bar (non-scrolling)
        hdr = tk.Canvas(parent, bg=BG2, height=18, highlightthickness=0)
        hdr.pack(fill=tk.X, padx=8)
        self._tl_hdr = hdr
        # headers drawn in _tl_draw_headers() after canvas has a width

        # Scrollable canvas — ALL rows drawn as canvas text items (zero widgets)
        sf = tk.Frame(parent, bg=BG)
        sf.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0, 4))

        vsb = tk.Scrollbar(sf, orient=tk.VERTICAL, bg=BG2, troughcolor=BG3,
                           activebackground=ACC)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)

        self._tl_canvas = tk.Canvas(sf, bg=BG3, highlightthickness=0,
                                    yscrollcommand=vsb.set)
        self._tl_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.config(command=self._tl_canvas.yview)

        # Data store — set once after analysis, never mutated during render
        self._tl_data   = []   # list of frame dicts
        self._tl_drawn  = False

        # Mouse-wheel scroll (Linux Button-4/5, Windows/Mac delta)
        for seq, delta in (('<MouseWheel>', None), ('<Button-4>', -3), ('<Button-5>', 3)):
            if delta is None:
                self._tl_canvas.bind(seq, lambda e: self._tl_canvas.yview_scroll(
                    int(-1 * (e.delta / 120)), 'units'))
            else:
                self._tl_canvas.bind(seq, lambda e, d=delta: self._tl_canvas.yview_scroll(d, 'units'))

        self._tl_canvas.bind('<Configure>', self._tl_on_resize)
        hdr.bind('<Configure>', lambda e: self._tl_draw_headers(e.width))

        # ── Per-second English translation panel (bottom) ─────────
        tk.Frame(parent, bg='#1a1a2e', height=1).pack(fill=tk.X, padx=8, pady=(4, 0))

        ps_hdr = tk.Frame(parent, bg=BG2, padx=8, pady=3)
        ps_hdr.pack(fill=tk.X)
        tk.Label(ps_hdr, text='PER-SECOND  ENGLISH  TRANSLATION',
                 font=FONT_LABEL, fg=ACC2, bg=BG2).pack(side=tk.LEFT)
        tk.Label(ps_hdr,
                 text='one line per second · dominant svara + rasa → closest English',
                 font=('Courier', 7), fg=MUTED, bg=BG2).pack(side=tk.LEFT, padx=12)

        self._ps_text = scrolledtext.ScrolledText(
            parent, height=8, font=('Courier', 9),
            bg=BG3, fg=BRIGHT, insertbackground=ACC,
            relief='flat', wrap=tk.WORD,
            state=tk.DISABLED,
        )
        self._ps_text.pack(fill=tk.X, padx=8, pady=(0, 6))

    def _tl_draw_headers(self, w=None):
        hdr = self._tl_hdr
        hdr.delete('all')
        W = w or hdr.winfo_width() or 800
        labels = [
            (self._TL_COL['bar'],  'ENERGY'),
            (self._TL_COL['time'], 'TIME'),
            (self._TL_COL['hz'],   'Hz'),
            (self._TL_COL['midi'], 'MIDI'),
            (self._TL_COL['haz'],  'HAZ / RASA'),
            (self._TL_COL['dev'],  'SVARA'),
            (self._TL_COL['iast'], 'SVARA NAME'),
            (self._TL_COL['eng'],  'ENGLISH MEANING'),
        ]
        for x, txt in labels:
            hdr.create_text(x + 2, 9, text=txt, anchor='w',
                            font=FONT_LABEL, fill=ACC2)

    def _tl_on_resize(self, event):
        # Re-render if data already loaded
        if self._tl_drawn and self._tl_data:
            self._tl_render_all()

    def _clear_timeline(self):
        self._tl_canvas.delete('all')
        self._tl_data  = []
        self._tl_drawn = False
        self._tl_progress.config(text='')
        self._ps_text.config(state=tk.NORMAL)
        self._ps_text.delete('1.0', tk.END)
        self._ps_text.config(state=tk.DISABLED)

    def _start_timeline_analysis(self):
        if not self._loaded_wav:
            tk.messagebox.showinfo('No File',
                'Please load a WAV (or MP3 with ffmpeg) on the AUDIO tab first.')
            return
        self._clear_timeline()
        self._tl_btn.config(state=tk.DISABLED)
        self._tl_progress.config(text='Analysing…')
        threading.Thread(target=self._timeline_thread, daemon=True).start()

    def _timeline_thread(self):
        try:
            path = self._loaded_wav

            last_pct = [-1]
            def _prog(fi, total):
                pct = int(100 * fi / max(total, 1))
                if pct != last_pct[0]:
                    last_pct[0] = pct
                    self.root.after(0, lambda p=pct:
                        self._tl_progress.config(text=f'Analysing… {p}%'))

            self._status_set('Running 0.1s frame analysis…')
            frames = analyse_audio_frames(path, frame_sec=0.1, progress_cb=_prog)

            # Hand data to main thread; render in one shot
            def _deliver(f=frames):
                self._tl_data = f
                self._tl_render_all()
                n   = len(f)
                dur = f[-1]['t_end'] if f else 0.0
                self._tl_progress.config(text=f'✓  {n} frames · {dur:.1f}s total')
                self._tl_btn.config(state=tk.NORMAL)
                self._status_set(f'Timeline complete: {n} frames.')
                self._tl_canvas.yview_moveto(0)

            self.root.after(0, _deliver)

        except Exception as e:
            self.root.after(0, lambda err=e: (
                self._tl_progress.config(text=f'Error: {err}'),
                self._tl_btn.config(state=tk.NORMAL),
                self._status_set(f'Timeline error: {err}'),
            ))

    def _tl_render_all(self):
        """
        Draw every frame as canvas text items in a single pass.
        No tkinter widgets are created — just canvas.create_text / create_rectangle.
        Handles 3600+ rows (6-min file) in under 1 second.
        """
        c      = self._tl_canvas
        data   = self._tl_data
        if not data:
            return

        c.delete('all')

        RH   = self._TL_ROW_H
        W    = c.winfo_width() or 900
        n    = len(data)
        total_h = n * RH

        # Set scroll region up front so scrollbar is correct immediately
        c.configure(scrollregion=(0, 0, W, total_h))

        COL  = self._TL_COL
        FN   = self._TL_FONT
        FNB  = self._TL_FONT_B
        # colour aliases (local lookup is faster)
        c_muted = MUTED; c_teal = TEAL; c_orange = ORANGE
        c_pink = PINK;   c_acc = ACC;   c_acc2 = ACC2
        c_bright = BRIGHT; c_bg3 = BG3; c_bg2 = BG2

        BAR_MAX = 60   # max energy-bar width in pixels

        for i, fr in enumerate(data):
            y_top = i * RH
            y_mid = y_top + RH // 2

            # Alternating row background
            row_bg = c_bg3 if i % 2 == 0 else c_bg2
            c.create_rectangle(0, y_top, W, y_top + RH,
                               fill=row_bg, outline='', tags='row')

            # Energy bar (coloured rectangle)
            ne = fr['norm_energy']
            bar_w = max(2, int(ne * BAR_MAX))
            bar_col = (c_teal if ne < 0.33 else c_acc if ne < 0.66 else RED)
            c.create_rectangle(COL['bar'], y_top + 3,
                               COL['bar'] + bar_w, y_top + RH - 3,
                               fill=bar_col, outline='', tags='bar')

            # TIME
            c.create_text(COL['time'], y_mid,
                          text=f'{fr["t_start"]:6.2f}s',
                          anchor='w', font=FN, fill=c_muted, tags='txt')
            # Hz
            c.create_text(COL['hz'], y_mid,
                          text=f'{fr["dom_hz"]:7.1f}',
                          anchor='w', font=FN, fill=c_teal, tags='txt')
            # MIDI
            c.create_text(COL['midi'], y_mid,
                          text=fr['midi_name'],
                          anchor='w', font=FNB, fill=c_orange, tags='txt')
            # HAZ dev + iast
            c.create_text(COL['haz'], y_mid,
                          text=f'{fr["haz_dev"]} {fr["haz_iast"]}',
                          anchor='w', font=FN, fill=c_pink, tags='txt')
            # Svara Devanagari
            c.create_text(COL['dev'], y_mid,
                          text=fr['svara_dev'],
                          anchor='w', font=FONT_DEV, fill=c_acc, tags='txt')
            # Svara IAST name
            c.create_text(COL['iast'], y_mid,
                          text=fr['svara_iast'],
                          anchor='w', font=FNB, fill=c_acc2, tags='txt')
            # English (truncated)
            eng = fr['english']
            if len(eng) > 72:
                eng = eng[:72] + '…'
            c.create_text(COL['eng'], y_mid,
                          text=eng,
                          anchor='w', font=FN, fill=c_bright, tags='txt')

        self._tl_drawn = True
        self._tl_draw_headers()
        self._tl_populate_per_second()

    # ── Per-second English sentence builder ──────────────────────

    def _tl_populate_per_second(self):
        """
        Group the 0.1s frames by whole second.
        For each second pick the dominant svara (most common svara_name),
        dominant rasa (most common haz_iast), and average Hz.
        Render one natural English sentence per second into the scrolled
        text box at the bottom of the timeline tab.
        """
        data = self._tl_data
        if not data:
            return

        # Group frames into per-second buckets
        from collections import Counter
        buckets = {}
        for fr in data:
            sec = int(fr['t_start'])
            if sec not in buckets:
                buckets[sec] = []
            buckets[sec].append(fr)

        lines = []
        for sec in sorted(buckets):
            frames = buckets[sec]
            t_end  = frames[-1]['t_end']

            # Dominant svara (by count)
            svara_counts  = Counter(fr['svara_name']  for fr in frames)
            rasa_counts   = Counter(fr['haz_iast']    for fr in frames)
            dom_svara     = svara_counts.most_common(1)[0][0]
            dom_rasa      = rasa_counts.most_common(1)[0][0]

            # Grab the first frame whose svara_name matches for full detail
            ref = next((fr for fr in frames if fr['svara_name'] == dom_svara), frames[0])

            avg_hz    = sum(fr['dom_hz']      for fr in frames) / len(frames)
            avg_nrg   = sum(fr['norm_energy'] for fr in frames) / len(frames)
            midi_name = ref['midi_name']
            dev       = ref['svara_dev']
            english   = ref['english']

            # Build a single human-readable sentence
            energy_word = ('quiet' if avg_nrg < 0.2 else
                           'moderate' if avg_nrg < 0.5 else
                           'strong'  if avg_nrg < 0.75 else 'intense')

            sentence = (
                f'[{sec:4d}s – {t_end:5.1f}s]  '
                f'{dev} {dom_svara}  ·  {midi_name} @ {avg_hz:.0f} Hz  '
                f'({energy_word} energy)  —  {english}  ·  rasa: {dom_rasa}'
            )
            lines.append(sentence)

        body = '\n'.join(lines)

        txt = self._ps_text
        txt.config(state=tk.NORMAL)
        txt.delete('1.0', tk.END)
        txt.insert(tk.END, body)
        txt.config(state=tk.DISABLED)
        txt.yview_moveto(0)

    # ─── SANSKRIT → ENGLISH ──────────────────────────────────────

    def _translate_sk_en(self):
        text = self._sk_in.get('1.0', tk.END).strip()
        if not text:
            return

        # Check for known mantra phrases first
        mantra = lookup_mantra(text)
        if mantra:
            iast, dev, lit, eng, notes = mantra
            self._set_text(self._sk_dev,  dev)
            self._set_text(self._sk_iast, iast)
            self._set_text(self._sk_lit,  lit)
            self._set_text(self._sk_en,   eng)
            self._set_text(self._sk_note, notes)
        else:
            lit, eng = translate_sanskrit_to_english(text)
            # Build Devanagari word-by-word
            words = text.lower().strip().split()
            devs  = []
            iasts = []
            for w in words:
                clean = w.strip('.,;:!?()')
                if clean in SANSKRIT_DICT:
                    devs.append(simple_devanagari(clean))
                    iasts.append(clean)
                else:
                    devs.append(f'[{w}]')
                    iasts.append(w)
            self._set_text(self._sk_dev,  ' '.join(devs))
            self._set_text(self._sk_iast, ' '.join(iasts))
            self._set_text(self._sk_lit,  lit)
            self._set_text(self._sk_en,   eng)
            self._set_text(self._sk_note, f'Translated {len(words)} word(s). Enter a known mantra for full commentary.')

        self._status_set('Sanskrit → English translation complete.')

    def _clear_sk_results(self):
        for w in [self._sk_dev, self._sk_iast, self._sk_lit, self._sk_en, self._sk_note]:
            self._set_text(w, '')

    # ─── ENGLISH → SANSKRIT ──────────────────────────────────────

    def _translate_en_sk(self):
        text = self._en_in.get('1.0', tk.END).strip()
        if not text:
            return
        iast, dev, note = translate_english_to_sanskrit(text)
        self._set_text(self._en_iast, iast)
        self._set_text(self._en_dev,  dev)
        self._set_text(self._en_note, note + '\n\n'
            'Sanskrit does not map word-for-word to English. Each word above is the\n'
            'closest Sanskrit concept. For precise translation, consult a Sanskrit scholar\n'
            'or Monier-Williams Sanskrit–English Dictionary.')
        self._status_set('English → Sanskrit translation complete.')

    def _clear_en_results(self):
        for w in [self._en_iast, self._en_dev, self._en_note]:
            self._set_text(w, '')

    # ─── TONE GENERATOR ──────────────────────────────────────────

    def _gen_tone(self, freq, tone_type='bowl'):
        self._stop_ev.set()
        time.sleep(0.05)
        self._stop_ev.clear()
        threading.Thread(target=self._tone_thread,
                         args=(freq, 5.0, tone_type), daemon=True).start()

    def _gen_custom_tone(self):
        try:
            freq = float(self._freq_var.get())
            dur  = float(self._dur_var.get())
            ttype = self._tone_type.get()
        except ValueError:
            messagebox.showerror('Input Error', 'Please enter valid numbers for frequency and duration.')
            return
        if not (10 <= freq <= 20000):
            messagebox.showerror('Input Error', 'Frequency must be between 10 and 20000 Hz.')
            return
        if not (0.5 <= dur <= 60):
            messagebox.showerror('Input Error', 'Duration must be between 0.5 and 60 seconds.')
            return
        self._stop_ev.set()
        time.sleep(0.05)
        self._stop_ev.clear()
        threading.Thread(target=self._tone_thread,
                         args=(freq, dur, ttype), daemon=True).start()

    def _gen_mantra_seq(self):
        try:
            freqs = [float(x.strip()) for x in self._seq_var.get().split(',') if x.strip()]
        except ValueError:
            messagebox.showerror('Input Error', 'Please enter comma-separated numbers.')
            return
        if not freqs:
            return
        self._stop_ev.set()
        time.sleep(0.05)
        self._stop_ev.clear()
        threading.Thread(target=self._seq_thread, args=(freqs,), daemon=True).start()

    def _tone_thread(self, freq, dur, tone_type):
        try:
            self._log(f'Synthesizing {tone_type} tone  {freq:.1f} Hz  {dur:.1f}s ...')
            self._status_set(f'Generating {freq:.1f} Hz tone...')
            ns = get_synth_ns()
            out = os.path.join(self._tmp_dir, f'tone_{int(freq)}_{int(time.time())}.wav')
            ns['render_sanskrit_tone'](out, freq=freq, duration=dur, tone_type=tone_type)
            self._log(f'✓ Generated: {Path(out).name}  ({os.path.getsize(out)//1024} KB)')
            self._status_set(f'Playing {freq:.1f} Hz...')
            play_wav(out, self._stop_ev)
            self._status_set('Done.')
            self._log('✓ Playback complete.')
        except Exception as e:
            self._log(f'✗ Error: {e}')
            self._status_set(f'Error: {e}')

    def _seq_thread(self, freqs):
        try:
            self._log(f'Synthesizing mantra sequence: {freqs}')
            self._status_set('Generating mantra sequence...')
            ns = get_synth_ns()
            out = os.path.join(self._tmp_dir, f'seq_{int(time.time())}.wav')
            ns['render_mantra_sequence'](out, freqs=freqs, duration=len(freqs)*1.2)
            self._log(f'✓ Generated: {Path(out).name}  ({os.path.getsize(out)//1024} KB)')
            self._status_set('Playing sequence...')
            play_wav(out, self._stop_ev)
            self._status_set('Done.')
            self._log('✓ Sequence playback complete.')
        except Exception as e:
            self._log(f'✗ Error: {e}')
            self._status_set(f'Error: {e}')

    # ─── RUN ─────────────────────────────────────────────────────

    def run(self):
        self.root.protocol('WM_DELETE_WINDOW', self._quit)
        self.root.mainloop()

    def _quit(self):
        self._stop_ev.set()
        try:
            shutil.rmtree(self._tmp_dir, ignore_errors=True)
        except Exception:
            pass
        try:
            self.root.destroy()
        except Exception:
            pass


if __name__ == '__main__':
    App().run()
