# Copyright 2009 The Go Authors.  All rights reserved.
# Use of this source code is governed by a BSD-style
# license that can be found in the LICENSE file.

include $(GOROOT)/src/Make.inc

TARG=gmp

# Can have plain GOFILES too, but this example doesn't.

CGOFILES=gmp.go

CGO_LDFLAGS=-lgmp

include $(GOROOT)/src/Make.pkg 