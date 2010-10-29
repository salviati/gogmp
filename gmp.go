// Copyright 2010 Utkan Güngördü.
// Based on $(GOROOT)/misc/cgo/gmp/gmp.go
// Released under the BSD-style license that can
// be found in Go's LICENSE file.

// Copyright 2009 The Go Authors.  All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

/*
In this package:
Float -> mpf_t
Int -> mpt_z
Rat -> mpf_q

Double -> float
Sint -> int
Uint -> uint

I know they don't look great ---but I had to do something
to avoid ambiguity.

I provided with the Clean() function as well, since GC
does not call destory() at this stage.
*/

/*
Garbage collection is the big problem.  It is fine for the Go world to
have pointers into the C world and to free those pointers when they
are no longer needed.  To help, the garbage collector calls an
object's destroy() method prior to collecting it.  C pointers can be
wrapped by Go objects with appropriate destroy methods.

It is much more difficult for the C world to have pointers into the Go
world, because the Go garbage collector is unaware of the memory
allocated by C.  The most important consideration is not to
constrain future implementations, so the rule is that Go code can
hand a Go pointer to C code but must separately arrange for
Go to hang on to a reference to the pointer until C is done with it.
*/

package gmp

// #include <gmp.h>
// #include <stdlib.h>
import "C"

import (
	"os"
	"unsafe"
	"strconv"
)

/*
 * one of a kind
 */

// An Int represents a signed multi-precision integer.
// The zero value for an Int represents the value 0.
type Int struct {
	i    C.mpz_t
	init bool
}

// NewInt returns a new Int initialized to x.
func NewInt(x int) *Int { return new(Int).SetSint(x) }

// Int promises that the zero value is a 0, but in gmp
// the zero value is a crash.  To bridge the gap, the
// init bool says whether this is a valid gmp value.
// doinit initializes z.i if it needs it.  This is not inherent
// to FFI, just a mismatch between Go's convention of
// making zero values useful and gmp's decision not to.
func (z *Int) doinit() {
	if z.init {
		return
	}
	z.init = true
	C.mpz_init(&z.i[0])
}

// Bytes returns z's representation as a big-endian byte array.
func (z *Int) Bytes() []byte {
	b := make([]byte, (z.Len()+7)/8)
	n := C.size_t(len(b))
	C.mpz_export(unsafe.Pointer(&b[0]), &n, 1, 1, 1, 0, &z.i[0])
	return b[0:n]
}

// Len returns the length of z in bits.  0 is considered to have length 1.
func (z *Int) Len() int {
	z.doinit()
	return int(C.mpz_sizeinbase(&z.i[0], 2))
}

// Set sets z = x and returns z.
func (z *Int) Set(x *Int) *Int {
	z.doinit()
	C.mpz_set(&z.i[0], &x.i[0])
	return z
}

// SetBytes interprets b as the bytes of a big-endian integer
// and sets z to that value.
func (z *Int) SetBytes(b []byte) *Int {
	z.doinit()
	if len(b) == 0 {
		z.SetSint(0)
	} else {
		C.mpz_import(&z.i[0], C.size_t(len(b)), 1, 1, 1, 0, unsafe.Pointer(&b[0]))
	}
	return z
}

// SetSint sets z = x and returns z.
func (z *Int) SetSint(x int) *Int {
	z.doinit()
	// TODO(rsc): more work on 32-bit platforms
	C.mpz_set_si(&z.i[0], C.long(x))
	return z
}

// Provided for compatibility with big package
func (z *Int) SetInt64(x int64) *Int {
	return z.SetSint(int(x))
}

// SetString interprets s as a number in the given base
// and sets z to that value.  The base must be in the range [2,36].
// SetString returns an error if s cannot be parsed or the base is invalid.
func (z *Int) SetString(s string, base int) os.Error {
	z.doinit()
	if base < 2 || base > 36 {
		return os.EINVAL
	}
	p := C.CString(s)
	defer C.free(unsafe.Pointer(p))
	if C.mpz_set_str(&z.i[0], p, C.int(base)) < 0 {
		return os.EINVAL
	}
	return nil
}

// String returns the decimal representation of z.
func (z *Int) String() string {
	s, _ := z.StringBase(10)
	return s
}

func (z *Int) StringBase(base int) (string, os.Error) {
	if z == nil {
		return "nil", nil
	}
	if base < 2 || base > 36 {
		return "", os.EINVAL
	}
	z.doinit()
	p := C.mpz_get_str(nil, C.int(base), &z.i[0])
	s := C.GoString(p)
	C.free(unsafe.Pointer(p))
	return s, nil
}

func (z *Int) destroy() {
	if z.init {
		C.mpz_clear(&z.i[0])
	}
	z.init = false
}
func (z *Int) Clear() {
	z.destroy()
}


/*
 * arithmetic
 */

// Add sets z = x + y and returns z.
func (z *Int) Add(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_add(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Sub sets z = x - y and returns z.
func (z *Int) Sub(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_sub(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Mul sets z = x * y and returns z.
func (z *Int) Mul(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_mul(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Div sets z = x / y, rounding toward zero, and returns z.
func (z *Int) Div(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_tdiv_q(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Mod sets z = x % y and returns z.
// Like the result of the Go % operator, z has the same sign as x.
func (z *Int) Mod(x, y *Int) *Int {
	x.doinit()
	y.doinit()
	z.doinit()
	C.mpz_tdiv_r(&z.i[0], &x.i[0], &y.i[0])
	return z
}

// Lsh sets z = x << s and returns z.
func (z *Int) Lsh(x *Int, s uint) *Int {
	x.doinit()
	z.doinit()
	C.mpz_mul_2exp(&z.i[0], &x.i[0], C.mp_bitcnt_t(s))
	return z
}

// Rsh sets z = x >> s and returns z.
func (z *Int) Rsh(x *Int, s uint) *Int {
	x.doinit()
	z.doinit()
	C.mpz_div_2exp(&z.i[0], &x.i[0], C.mp_bitcnt_t(s))
	return z
}

// Exp sets z = x^y % m and returns z.
// If m == nil, Exp sets z = x^y.
func (z *Int) Exp(x, y, m *Int) *Int {
	m.doinit()
	x.doinit()
	y.doinit()
	z.doinit()
	if m == nil {
		C.mpz_pow_ui(&z.i[0], &x.i[0], C.mpz_get_ui(&y.i[0]))
	} else {
		C.mpz_powm(&z.i[0], &x.i[0], &y.i[0], &m.i[0])
	}
	return z
}

func (z *Int) Sint() int {
	if !z.init {
		return 0
	}
	return int(C.mpz_get_si(&z.i[0]))
}

// Provided for compatibility with big package
func (z *Int) Int64() int64 {
	return int64(z.Sint())
}

// Neg sets z = -x and returns z.
func (z *Int) Neg(x *Int) *Int {
	x.doinit()
	z.doinit()
	C.mpz_neg(&z.i[0], &x.i[0])
	return z
}

// Abs sets z to the absolute value of x and returns z.
func (z *Int) Abs(x *Int) *Int {
	x.doinit()
	z.doinit()
	C.mpz_abs(&z.i[0], &x.i[0])
	return z
}


/*
 * functions without a clear receiver
 */

// CmpInt compares x and y. The result is
//
//   -1 if x <  y
//    0 if x == y
//   +1 if x >  y
//
func CmpInt(x, y *Int) int {
	x.doinit()
	y.doinit()
	switch cmp := C.mpz_cmp(&x.i[0], &y.i[0]); {
	case cmp < 0:
		return -1
	case cmp == 0:
		return 0
	}
	return +1
}

// DivModInt sets q = x / y and r = x % y.
func DivModInt(q, r, x, y *Int) {
	q.doinit()
	r.doinit()
	x.doinit()
	y.doinit()
	C.mpz_tdiv_qr(&q.i[0], &r.i[0], &x.i[0], &y.i[0])
}

// GcdInt sets d to the greatest common divisor of a and b,
// which must be positive numbers.
// If x and y are not nil, GcdInt sets x and y such that d = a*x + b*y.
// If either a or b is not positive, GcdInt sets d = x = y = 0.
func GcdInt(d, x, y, a, b *Int) {
	d.doinit()
	x.doinit()
	y.doinit()
	a.doinit()
	b.doinit()
	C.mpz_gcdext(&d.i[0], &x.i[0], &y.i[0], &a.i[0], &b.i[0])
}

// ProbablyPrime performs n Miller-Rabin tests to check whether z is prime.
// If it returns true, z is prime with probability 1 - 1/4^n.
// If it returns false, z is not prime.
func (z *Int) ProbablyPrime(n int) bool {
	z.doinit()
	return int(C.mpz_probab_prime_p(&z.i[0], C.int(n))) > 0
}

















type Float struct {
	i C.mpf_t
	init bool
	prec uint // 0 = use the default precision
}

// NewInt returns a new Int initialized to x.
func NewFloat(x float) *Float { return new(Float).SetDouble(x) }

// NewInt returns a new Int initialized to x, with precision prec.
func NewFloat2(x float, prec uint) *Float {
	f := new(Float)
	f.prec = prec
	f.SetDouble(x)
	return f
}

// Int promises that the zero value is a 0, but in gmp
// the zero value is a crash.  To bridge the gap, the
// init bool says whether this is a valid gmp value.
// doinit initializes f.i if it needs it.  This is not inherent
// to FFI, just a mismatch between Go's convention of
// making zero values useful and gmp's decision not to.
func (f *Float) doinit() {
	if f.init {
		return
	}
	if f.prec != 0 {
		C.mpf_init2(&f.i[0], C.mp_bitcnt_t(f.prec))
	} else {
		C.mpf_init(&f.i[0])
	}
	f.init = true
}

// Set sets f = x and returns f.
func (f *Float) Set(x *Float) *Float {
	f.doinit()
	C.mpf_set(&f.i[0], &x.i[0])
	return f
}

// SetInt sets f = x and returns f.
func (f *Float) SetSint(x int) *Float {
	f.doinit()
	C.mpf_set_si(&f.i[0], C.long(x))
	return f
}

// SetDouble sets f = x and returns f.
func (f *Float) SetDouble(x float) *Float {
	f.doinit()
	C.mpf_set_d(&f.i[0], C.double(x))
	return f
}

// SetString interprets s as a number in the given base
// and sets f to that value.  The base must be in the range [2,36].
// SetString returns an error if s cannot be parsed or the base is invalid.
func (f *Float) SetString(s string, base int) os.Error {
	f.doinit()
	if base < 2 || base > 36 {
		return os.EINVAL
	}
	p := C.CString(s)
	defer C.free(unsafe.Pointer(p))
	if C.mpf_set_str(&f.i[0], p, C.int(base)) < 0 {
		return os.EINVAL
	}
	return nil
}

func (f *Float) StringBase(base int, ndigits uint) (string, os.Error) {
	if f == nil {
		return "nil", nil
	}
	if base < 2 || base > 36 {
		return "", os.EINVAL
	}
	f.doinit()
	var exp_ C.mp_exp_t
	p := C.mpf_get_str(nil, &exp_, C.int(base), C.size_t(ndigits), &f.i[0])
	exp := int(exp_)
	s := C.GoString(p)
	C.free(unsafe.Pointer(p))

	if len(s) == 0 {return "0", nil}
	
	if exp > 0 && exp < len(s) {
		return s[:exp] + "." + s[exp:], nil
	}
	return s + "e" + strconv.Itoa(exp), nil
}

// String returns the decimal representation of z.
func (f *Float) String() string {
	s, _ := f.StringBase(10, 0)
	return s
}

func (f *Float) Double() float {
	f.doinit()
	return float(C.mpf_get_d(&f.i[0]))
}

 
func (f *Float) Sint() int {
	f.doinit()
	return int(C.mpf_get_si(&f.i[0]))
}


 /* 
  * Convert f to a `double', truncating if necessary (ie. rounding
  * towards zero), and with an exponent returned separately.
  */
func (f *Float) Double2Exp() (d float, exp int) {
	var exp_ C.long
	d = float(C.mpf_get_d_2exp(&exp_, &f.i[0]))
	exp = int(exp_)
 	return
}

func (f *Float) destroy() {
	if f.init {
		C.mpf_clear(&f.i[0])
	}
	f.init = false
}

func (f *Float) Clear() {
	f.destroy()
}

func (f *Float) GetPrec() uint {
	f.doinit()
	return uint(C.mpf_get_prec(&f.i[0]))
}

func (f *Float) SetPrec(prec uint) {
	f.doinit()
	C.mpf_set_prec(&f.i[0], C.mp_bitcnt_t(prec))
	f.prec = prec
}

func (f *Float) SetPrecRaw(prec uint) {
	f.doinit()
	C.mpf_set_prec_raw(&f.i[0], C.mp_bitcnt_t(prec))
}

func SetDefaultPrec(prec uint) {
	C.mpf_set_default_prec(C.mp_bitcnt_t(prec))
}

func GetDefaultPrec() uint {
	return uint(C.mpf_get_default_prec())
}

/*
 * arithmetic
 */

// Add sets f = x + y and returns f.
func (f *Float) Add(x, y *Float) *Float {
	x.doinit()
	y.doinit()
	f.doinit()
	C.mpf_add(&f.i[0], &x.i[0], &y.i[0])
	return f
}


func (f *Float) AddUint(x *Float, y uint) *Float {
	x.doinit()
	f.doinit()
	C.mpf_add_ui(&f.i[0], &x.i[0], C.ulong(y))
	return f
}

// Sub sets f = x - y and returns f.
func (f *Float) Sub(x, y *Float) *Float {
	x.doinit()
	y.doinit()
	f.doinit()
	C.mpf_sub(&f.i[0], &x.i[0], &y.i[0])
	return f
}

func (f *Float) SubUint(x *Float, y uint) *Float {
	x.doinit()
	f.doinit()
	C.mpf_sub_ui(&f.i[0], &x.i[0], C.ulong(y))
	return f
}

// Mul sets f = x * y and returns f.
func (f *Float) Mul(x, y *Float) *Float {
	x.doinit()
	y.doinit()
	f.doinit()
	C.mpf_mul(&f.i[0], &x.i[0], &y.i[0])
	return f
}

func (f *Float) MulUint(x *Float, y uint) *Float {
	x.doinit()
	f.doinit()
	C.mpf_mul_ui(&f.i[0], &x.i[0], C.ulong(y))
	return f
}

// Div sets f = x / y and returns f.
func (f *Float) Div(x, y *Float) *Float {
	x.doinit()
	y.doinit()
	f.doinit()
	C.mpf_div(&f.i[0], &x.i[0], &y.i[0])
	return f
}

func (f *Float) DivUint(x *Float, y uint) *Float {
	x.doinit()
	f.doinit()
	C.mpf_div_ui(&f.i[0], &x.i[0], C.ulong(y))
	return f
}

func (f *Float) UintDiv(x uint, y *Float) *Float {
	y.doinit()
	f.doinit()
	C.mpf_ui_div(&f.i[0], C.ulong(x), &y.i[0])
	return f
}

// Sqrt sets f = Sqrt(x) and returns f.
func (f *Float) Sqrt(x *Float) *Float {
	x.doinit()
	f.doinit()
	C.mpf_sqrt(&f.i[0], &x.i[0])
	return f
}

// Sqrt sets f = Sqrt(x) and returns f.
func (f *Float) SqrtUint(x uint) *Float {
	f.doinit()
	C.mpf_sqrt_ui(&f.i[0], C.ulong(x))
	return f
}

// PowUint sets f = x^y and returns f
func (f *Float) PowUint(x *Float, y uint) *Float {
	x.doinit()
	f.doinit()
	C.mpf_pow_ui(&f.i[0], &x.i[0], C.ulong(y))
	return f
}

// Neg sets z = -x and returns z.
func (f *Float) Neg(x *Float) *Float {
	x.doinit()
	f.doinit()
	C.mpf_neg(&f.i[0], &x.i[0])
	return f
}

// Abs sets z to the absolute value of x and returns z.
func (f *Float) Abs(x *Float) *Float {
	x.doinit()
	f.doinit()
	C.mpf_abs(&f.i[0], &x.i[0])
 	return f
}

// Mul2Exp sets z = x * 2^s and returns z.
func (f *Float) Mul2Exp(x *Float, s uint) *Float {
	x.doinit()
	f.doinit()
	C.mpf_mul_2exp(&f.i[0], &x.i[0], C.mp_bitcnt_t(s))
	return f
}

// Div2Exp sets z = x / 2^s and returns z.
func (f *Float) Div2Exp(x *Float, s uint) *Float {
	x.doinit()
	f.doinit()
	C.mpf_div_2exp(&f.i[0], &x.i[0], C.mp_bitcnt_t(s))
	return f
}


/* 
 * Comparison
 * /


/* Compute the relative difference between x and y and store the
      result in f.  This is abs(x-y)/x. */

func (f *Float) RelDiff(x, y *Float) *Float {
	x.doinit()
	y.doinit()
	f.doinit()
	C.mpf_reldiff(&f.i[0], &x.i[0], &y.i[0])
	return f
}

/* Return +1 if f > 0, 0 if f = 0, and -1 if f < 0. */
func (f *Float) Sgn() int {
	f.doinit()
	//TODO(ug): mpf_sgn seems to be implemented as a macro.
	// We need to watch out for changes in the data structure :(

	//return int(C.mpf_sgn(&f.i[0]))
	switch size := int(f.i[0]._mp_size); {
	case size < 0:
		return -1
	case size == 0:
		return 0
	}
	return 1
}


/*
 * functions without a clear receiver
 */

// CmpInt compares x and y. The result is
//
//   neg if x <  y
//    0 if x == y
//   pos if x >  y
//

func CmpFloat(x, y *Float) int {
	x.doinit()
	y.doinit()
	return int(C.mpf_cmp(&x.i[0], &y.i[0]))
}

func CmpFloatDouble(x *Float, y float) int {
	x.doinit()
	return int(C.mpf_cmp_d(&x.i[0], C.double(y)))
}

func CmpFloatUint(x *Float, y uint) int {
	x.doinit()
	return int(C.mpf_cmp_ui(&x.i[0], C.ulong(y)))
}

func CmpFloatSint(x *Float, y int) int {
	x.doinit()
	return int(C.mpf_cmp_si(&x.i[0], C.long(y)))
}

/* Return non-zero if the first n bits of x and y are equal,
      zero otherwise.  I.e., test if x and y are approximately equal. */
func EqFloat(x, y *Float, n uint) int {
	x.doinit()
	y.doinit()
	return int(C.mpf_eq(&x.i[0], &y.i[0], C.ulong(n)))
}

func SwapFloat(x, y *Float) {
	x.doinit()
	y.doinit()
	C.mpf_swap(&x.i[0], &y.i[0])
}

// Sets f = Ceil(x) and returns f.
func (f *Float) Ceil(x *Float) *Float {
	x.doinit()
	f.doinit()
	C.mpf_ceil(&f.i[0], &x.i[0])
	return f
}

// Sets f = Floor(x) and returns f.
func (f *Float) Floor(x *Float) *Float {
	x.doinit()
	f.doinit()
	C.mpf_floor(&f.i[0], &x.i[0])
	return f
}

// Sets f = Trunc(x) (=round towards zero) and returns f.
func (f *Float) Trunc(x *Float) *Float {
	x.doinit()
	f.doinit()
	C.mpf_trunc(&f.i[0], &x.i[0])
	return f
}

func (f *Float) IsInteger() bool {
	f.doinit()
	return int(C.mpf_integer_p(&f.i[0])) != 0
}

//TODO(ug) mpf_fits_* and random functions


type Rat struct {
	i C.mpq_t
	init bool
}

// NewRat returns a new Rat initialized to x/y.
func NewRat(x int, y uint) *Rat { return new(Rat).SetSint(x,y) }

// Int promises that the zero value is a 0, but in gmp
// the zero value is a crash.  To bridge the gap, the
// init bool says whether this is a valid gmp value.
// doinit initializes z.i if it needs it.  This is not inherent
// to FFI, just a mismatch between Go's convention of
// making zero values useful and gmp's decision not to.
func (q *Rat) doinit() {
	if q.init {
		return
	}
	q.init = true
	C.mpq_init(&q.i[0])
}

// Set sets z = x and returns z.
func (q *Rat) Set(x *Rat) *Rat {
	q.doinit()
	C.mpq_set(&q.i[0], &x.i[0])
	return q
}

// SetSint sets q to x/y and returns q.
func (q *Rat) SetSint(x int y uint) *Rat {
	q.doinit()
	C.mpq_set_si(&q.i[0], C.long(x), C.ulong(y))
	return q
}

// SetUint sets q to x/y and returns q.
func (q *Rat) SetUint(x, y uint) *Rat {
	q.doinit()
	C.mpq_set_ui(&q.i[0], C.ulong(x), C.ulong(y))
	return q
}

// SetInt sets q to x and returns q.
func (q *Rat) SetInt(x *Int) *Rat {
	q.doinit()
	x.doinit()
	C.mpq_set_z(&q.i[0], &x.i[0])
	return q
}

// SetString interprets s as a number in the given base
// and sets z to that value.  The base must be in the range [2,36].
// SetString returns an error if s cannot be parsed or the base is invalid.
func (q *Rat) SetString(s string, base int) os.Error {
	q.doinit()
	if base < 2 || base > 36 {
		return os.EINVAL
	}
	p := C.CString(s)
	defer C.free(unsafe.Pointer(p))
	if C.mpq_set_str(&q.i[0], p, C.int(base)) < 0 {
		return os.EINVAL
	}
	return nil
}

func SwapRat(x, y *Rat) {
	x.doinit()
	y.doinit()
	C.mpq_swap(&x.i[0], &y.i[0])
}

// String returns the decimal representation of z.
func (q *Rat) StringBase(base int) (string, os.Error) {
	if q == nil {
		return "nil", nil
	}
	if base < 2 || base > 36 {
		return "", os.EINVAL
	}
	q.doinit()
	p := C.mpq_get_str(nil, C.int(base), &q.i[0])
	s := C.GoString(p)
	C.free(unsafe.Pointer(p))
	return s, nil
}

func (q *Rat) String() string {
	s, _ := q.StringBase(10)
	return s
}

func (q *Rat) Double() float {
	q.doinit()
	return float(C.mpq_get_d(&q.i[0]))
}

// SetDouble sets f = x and returns q.
func (q *Rat) SetDouble(x float) *Rat {
	q.doinit()
	C.mpq_set_d(&q.i[0], C.double(x))
	return q
}

// SetFloat sets f = x and returns f.
func (q *Rat) SetFloat(x *Float) *Rat {
	q.doinit()
	C.mpq_set_f(&q.i[0], &x.i[0])
	return q
}


func (q *Rat) destroy() {
	if q.init {
		C.mpq_clear(&q.i[0])
	}
	q.init = false
}

func (q *Rat) Clear() {
	q.destroy()
}

// Add sets q = x + y and returns f.
func (q *Rat) Add(x, y *Rat) *Rat {
	x.doinit()
	y.doinit()
	q.doinit()
	C.mpq_add(&q.i[0], &x.i[0], &y.i[0])
	return q
}

func (q *Rat) Sub(x, y *Rat) *Rat {
	x.doinit()
	y.doinit()
	q.doinit()
	C.mpq_sub(&q.i[0], &x.i[0], &y.i[0])
	return q
}

func (q *Rat) Mul(x, y *Rat) *Rat {
	x.doinit()
	y.doinit()
	q.doinit()
	C.mpq_mul(&q.i[0], &x.i[0], &y.i[0])
	return q
}

func (q *Rat) Div(x, y *Rat) *Rat {
	x.doinit()
	y.doinit()
	q.doinit()
	C.mpq_div(&q.i[0], &x.i[0], &y.i[0])
	return q
}

func (q *Rat) Abs(x *Rat) *Rat {
	x.doinit()
	q.doinit()
	C.mpq_abs(&q.i[0], &x.i[0])
	return q
}

func (q *Rat) Inv(x *Rat) *Rat {
	x.doinit()
	q.doinit()
	C.mpq_inv(&q.i[0], &x.i[0])
	return q
}

// Mul2Exp sets z = x * 2^s and returns z.
func (q *Rat) Mul2Exp(x *Rat, s uint) *Rat {
	x.doinit()
	q.doinit()
	C.mpq_mul_2exp(&q.i[0], &x.i[0], C.mp_bitcnt_t(s))
	return q
}

// Div2Exp sets z = x / 2^s and returns z.
func (q *Rat) Div2Exp(x *Rat, s uint) *Rat {
	x.doinit()
	q.doinit()
	C.mpq_div_2exp(&q.i[0], &x.i[0], C.mp_bitcnt_t(s))
	return q
}

func CmpRat(x, y *Rat) int {
	x.doinit()
	y.doinit()
	return int(C.mpq_cmp(&x.i[0],&y.i[0]))
}

func CmpRatUint(q *Rat, x, y uint) int {
	q.doinit()
	return 0 // FIXME(ug): Macro...
	//return int(C.mpq_cmp_ui(&x.i[0], C.ulong(x), C.ulong(y)))
}

func CmpRatSint(q *Rat, x int, y uint) int {
	q.doinit()
	return 0 // FIXME(ug): Macro...
	//return int(C.mpq_cmp_ui(&x.i[0], C.long(x), C.ulong(y)))
}

func (q *Rat) Sgn() int {
	q.doinit()
	//TODO(ug): mpf_sgn seems to be implemented as a macro.
	// We need to watch out for changes in the data structure :(

	//return int(C.mpq_sgn(&f.i[0]))
	switch size := int(q.i[0]._mp_num._mp_size); {
	case size < 0:
		return -1
	case size == 0:
		return 0
	}
	return 1
}

func EqRat(x, y *Rat) bool {
	x.doinit()
	y.doinit()
	return C.mpq_equal(&x.i[0], &y.i[0]) != 0
}

func (q *Rat) Num(n *Int) *Int {
	q.doinit()
	n.doinit()
	C.mpq_get_num(&n.i[0], &q.i[0])
	return n
}

func (q *Rat) Den(n *Int) *Int {
	q.doinit()
	n.doinit()
	C.mpq_get_den(&n.i[0], &q.i[0])
	return n
}

func (q *Rat) SetNum(n *Int) *Rat {
	q.doinit()
	n.doinit()
	C.mpq_set_num(&q.i[0], &n.i[0])
	return q
}

func (q *Rat) SetDen(n *Int) *Rat {
	q.doinit()
	n.doinit()
	C.mpq_set_den(&q.i[0], &n.i[0])
	return q
}

// TODO(ug): mpq_numref, mpq_denref 
