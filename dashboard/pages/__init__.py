"""
Nyquist Dashboard Pages Package

Each page is a separate module with a render() function.
Explicitly import all page modules to ensure they are available.
"""

# Import all page modules using relative imports
# Using actual filenames on disk (case-sensitive for Linux)
from . import Overview
from . import personas
from . import Stackup
from . import AI_ARMADA
from . import tests
from . import metrics
from . import omega
from . import avlar
from . import roadmap
from . import glossary
from . import publications
from . import matrix
from . import faq
from . import unknown
from . import debug

# Export all page modules
__all__ = [
    'Overview',
    'personas',
    'Stackup',
    'AI_ARMADA',
    'tests',
    'metrics',
    'omega',
    'avlar',
    'roadmap',
    'glossary',
    'publications',
    'matrix',
    'faq',
    'unknown',
    'debug',
]
