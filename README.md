# V01D Audio → Sanskrit Translator · v0.1 Alpha

> *Pure Python · Zero dependencies · Single file · MIT License*  
> Part of the [EONS OF THE CYBERV01D5](https://github.com/eonstoeons) suite.

---

## What it does

Loads audio files (MP3 / WAV), performs pitch analysis frame-by-frame, and maps dominant frequencies to **Sanskrit svara** (melodic tones) and **rasa** (emotional essence) — outputting human-readable Devanagari, IAST transliteration, MIDI note names, Hz values, and energy levels per second.

Also works in reverse:

| Direction | Input | Output |
|---|---|---|
| Audio → Sanskrit | MP3 / WAV file | Svara · rasa · Devanagari · IAST · Hz |
| Sanskrit → English | IAST or Devanagari text | Literal meaning · English translation · grammatical notes |
| English → Sanskrit | Plain English words | IAST transliteration · Devanagari · contextual notes |

---

## Features

- **Audio analysis** — frame-by-frame pitch detection, svara/rasa classification, energy profiling
- **Sanskrit ↔ English engine** — offline rule-based; covers Vedic vocabulary, mantras, chakras, Samkhya, grammar particles
- **Mantra library** — full commentary on Gayatri, Maha Mrityunjaya, Om Namah Shivaya, and more
- **IAST → Devanagari rendering** — heuristic converter covering the full classical consonant/vowel table
- **Embedded PyAmby synthesis** — generates Tibetan singing bowl tones, veena-timbre Karplus-Strong mantra sequences, and drone pads at any frequency (10–20 000 Hz)
- **Tone sequencer** — enter comma-separated Hz values to render and play a chanted syllable sequence
- **Zero install** — runs on any Python 3.8+ with tkinter (standard on all platforms)

---

## Requirements

- Python 3.8+
- `tkinter` (included in the standard library / most OS Python distributions)
- No pip installs. No wheels. No venv required.

---

## Run

```bash
python V01D_Audio_to_Sanksrit_Translator_0_1_Alpha.py
```

---

## Tabs

| Tab | Purpose |
|---|---|
| **Audio → Sanskrit** | Load file, run analysis, read svara/rasa timeline |
| **Sanskrit → English** | Paste IAST text, get literal + English translation |
| **English → Sanskrit** | Type English words, get IAST + Devanagari |
| **Tone Generator** | Synthesize and play Sanskrit-toned audio |

---

## Notes

This is a **v0.1 Alpha**. The Sanskrit dictionary covers core Vedic and Tantric vocabulary (~120 roots). Audio pitch detection is FFT-based and works best on monophonic or drone-heavy recordings. It is not speech-to-text — it maps *pitch content* to melodic/emotional Sanskrit categories.

For precise scholarly translation, consult the Monier-Williams Sanskrit–English Dictionary.

---

## License

MIT · Collaboration: [eonstoeons](https://github.com/eonstoeons) × Claude (Anthropic)  
Archived at [archive.org/details/i-am-dao](https://archive.org/details/i-am-dao)
