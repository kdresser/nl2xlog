import os.path, sys

def pfx2pp(p):
  """Put p after '' at head for list."""
  if p in sys.path:
    return
  sys.path.insert(1, p)

def set():
  pfx2pp('N:\\P\\G\\plib2')
