from distutils.core import setup, Extension
from distutils.sysconfig import get_python_inc

import os

if __name__ == '__main__':
    setup(name="FAdo",
          packages=["FAdo"],
          version="1.0",
          description="Formal Languages Manipulation Tools",
          requires=["yappy"],
          provides=["FAdo"],
          ext_package="FAdo",
          install_requires=["future"],
          author="Rogerio Reis and Nelma Moreira",
          author_email="{rvr,nam}@dcc.fc.up.pt",
          url="http://www.dcc.fc.up.pt/FAdo",
          maintainer="Rogerio Reis",
          maintainer_email="rvr@dcc.fc.up.pt")
