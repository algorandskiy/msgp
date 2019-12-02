package gen

import (
	"io"
)

func isZeros(w io.Writer) *isZeroGen {
	return &isZeroGen{
		p: printer{w: w},
	}
}

type isZeroGen struct {
	passes
	p   printer
	ctx *Context
}

func (s *isZeroGen) Method() Method { return IsZero }

func (s *isZeroGen) Apply(dirs []string) error {
	return nil
}

func (s *isZeroGen) Execute(p Elem) error {
	if !s.p.ok() {
		return s.p.err
	}
	p = s.applyall(p)
	if p == nil {
		return nil
	}
	if !IsPrintable(p) {
		return nil
	}

	s.ctx = &Context{}
	s.ctx.PushString(p.TypeName())

	s.p.comment("MsgIsZero returns whether this is a zero value")

	s.p.printf("\nfunc (%s %s) MsgIsZero() bool { return %s }", p.Varname(), p.TypeName(), p.IfZeroExpr())
	return s.p.err
}