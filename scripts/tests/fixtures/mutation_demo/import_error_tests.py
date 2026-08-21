"""A control module that does not LOAD, so the harness's build probe has something to catch.

Syntactically valid -- `py_compile` accepts it -- and it raises the moment it is
imported.  That is the half of `DID NOT BUILD` a syntax check cannot see, and the
half that otherwise arrives as `ERROR:` lines and is scored as a kill.
"""

from __future__ import annotations

raise RuntimeError("this fixture cannot be imported, on purpose")
