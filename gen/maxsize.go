package gen

import (
	"bytes"
	"fmt"
	"go/ast"
	"io"
	"reflect"
	"strconv"
	"strings"

	"github.com/algorand/msgp/msgp"
)

func maxSizes(w io.Writer, topics *Topics) *maxSizeGen {
	return &maxSizeGen{
		p:      printer{w: w},
		state:  assign,
		topics: topics,
	}
}

type maxSizeGen struct {
	passes
	p      printer
	state  sizeState
	ctx    *Context
	topics *Topics
}

func (s *maxSizeGen) Method() Method { return MaxSize }

func (s *maxSizeGen) Apply(dirs []string) error {
	return nil
}

// this lets us chain together addition
// operations where possible
func (s *maxSizeGen) addConstant(sz string) {
	if !s.p.ok() {
		return
	}

	switch s.state {
	case assign:
		s.p.print("\ns = " + sz)
		s.state = expr
		return
	case add:
		s.p.print("\ns += " + sz)
		s.state = expr
		return
	case expr:
		s.p.print(" + " + sz)
		return
	}

	panic("unknown size state")
}

func (s *maxSizeGen) Execute(p Elem) ([]string, error) {
	if !s.p.ok() {
		return nil, s.p.err
	}
	p = s.applyall(p)
	if p == nil {
		return nil, nil
	}

	// We might change p.Varname in methodReceiver(); make a copy
	// to not affect other code that will use p.
	p = p.Copy()

	s.p.comment("MaxSize returns a maximum valid message size for this message type")

	if IsDangling(p) {
		baseType := p.(*BaseElem).IdentName
		ptrName := p.Varname()
		receiver := methodReceiver(p)
		s.p.printf("\nfunc %s int{", getMaxSizeMethod(p.TypeName()))
		s.p.printf("\n  return ((*(%s))(%s)).MaxSize()", baseType, ptrName)
		s.p.printf("\n}")
		s.topics.Add(receiver, "MaxSize")
		return nil, s.p.err
	}

	s.ctx = &Context{}
	s.ctx.PushString(p.TypeName())

	receiver := imutMethodReceiver(p)
	s.p.printf("\nfunc  %s (s int) {", getMaxSizeMethod(p.TypeName()))
	s.state = assign
	next(s, p)
	s.p.nakedReturn()
	// Unnecessary for "static" method but need to keep it for rest of the code to work for now TODO: remove
	s.topics.Add(receiver, "MaxSize")
	return nil, s.p.err
}

func (s *maxSizeGen) gStruct(st *Struct) {
	if !s.p.ok() {
		return
	}

	nfields := uint32(0)
	for i := range st.Fields {
		if ast.IsExported(st.Fields[i].FieldName) {
			nfields += 1
		}
	}

	if st.AsTuple {
		data := msgp.AppendArrayHeader(nil, nfields)
		s.addConstant(strconv.Itoa(len(data)))
		for i := range st.Fields {
			if !ast.IsExported(st.Fields[i].FieldName) {
				continue
			}

			if !s.p.ok() {
				return
			}
			next(s, st.Fields[i].FieldElem)
		}
	} else {
		data := msgp.AppendMapHeader(nil, nfields)
		s.addConstant(strconv.Itoa(len(data)))
		for i := range st.Fields {
			if !ast.IsExported(st.Fields[i].FieldName) {
				continue
			}

			data = data[:0]
			data = msgp.AppendString(data, st.Fields[i].FieldTag)
			s.addConstant(strconv.Itoa(len(data)))
			next(s, st.Fields[i].FieldElem)
		}
	}
}

func (s *maxSizeGen) gPtr(p *Ptr) {
	s.state = add // inner must use add
	next(s, p.Value)
	s.state = add // closing block; reset to add
}

func (s *maxSizeGen) gSlice(sl *Slice) {
	if !s.p.ok() {
		return
	}
	if (sl.AllocBound() == "" || sl.AllocBound() == "-") && (sl.TotalAllocBound() == "" || sl.TotalAllocBound() == "-") {
		s.p.printf("\npanic(\"Slice %s is unbounded\")", sl.Varname())
		s.state = add // reset the add to prevent further + expressions from being added to the end the panic statement
		return
	}

	s.addConstant(builtinSize(arrayHeader))

	// use the total allocbound if it's available
	if sl.common.TotalAllocBound() != "" && sl.common.TotalAllocBound() != "-" {
		s.addConstant(sl.common.TotalAllocBound())
		return
	}

	topLevelAllocBound := sl.AllocBound()
	if sl.Els.AllocBound() == "" && len(strings.Split(sl.AllocBound(), ",")) > 1 {
		splitIndex := strings.Index(sl.AllocBound(), ",")
		sl.Els.SetAllocBound(sl.AllocBound()[splitIndex+1:])
		topLevelAllocBound = sl.AllocBound()[:splitIndex]
	}

	// if the slice's element is a fixed size
	// (e.g. float64, [32]int, etc.), then
	// print the allocbound times the element size directly
	if str, err := fixedMaxSizeExpr(sl.Els); err == nil {
		s.addConstant(fmt.Sprintf("((%s) * (%s))", topLevelAllocBound, str))
		return
	} else {
		s.p.printf("\npanic(\"Unable to determine max size: %s\")", err)
		s.state = add // reset the add to prevent further + expressions from being added to the end the panic statement
		return
	}
}

func (s *maxSizeGen) gArray(a *Array) {
	if !s.p.ok() {
		return
	}

	s.addConstant(builtinSize(arrayHeader))

	// if the array's children are a fixed
	// size, we can compile an expression
	// that always represents the array's wire size
	if str, err := fixedMaxSizeExpr(a); err == nil {
		s.addConstant(fmt.Sprintf("((%s) * (%s))", a.Size, str))
		return
	} else {
		s.p.printf("\npanic(\"Unable to determine max size: %s\")", err)
		s.state = add // reset the add to prevent further + expressions from being added to the end the panic statement
		return

	}
}

func (s *maxSizeGen) gMap(m *Map) {
	s.addConstant(builtinSize(mapHeader))
	vn := m.Varname()
	s.p.printf("\nif %s != nil {", vn)
	s.p.printf("\nfor %s, %s := range %s {", m.Keyidx, m.Validx, vn)
	s.p.printf("\n_ = %s", m.Keyidx) // we may not use the key
	s.p.printf("\n_ = %s", m.Validx) // we may not use the value
	s.p.printf("\ns += 0")
	s.state = expr
	s.ctx.PushVar(m.Keyidx)
	next(s, m.Key)
	next(s, m.Value)
	s.ctx.Pop()
	s.p.closeblock()
	s.p.closeblock()
	s.state = add
}

func (s *maxSizeGen) gBase(b *BaseElem) {
	if !s.p.ok() {
		return
	}
	if b.Convert && b.ShimMode == Convert {
		s.state = add
		vname := randIdent()
		s.p.printf("\nvar %s %s", vname, b.BaseType())

		// ensure we don't get "unused variable" warnings from outer slice iterations
		s.p.printf("\n_ = %s", b.Varname())

		value, err := baseMaxSizeExpr(b.Value, vname, b.BaseName(), b.TypeName(), b.common.AllocBound())
		if err != nil {
			s.p.printf("\npanic(\"Unable to determine max size: %s\")", err)
			s.state = add // reset the add to prevent further + expressions from being added to the end the panic statement
			return
		}
		s.p.printf("\ns += %s", value)
		s.state = expr

	} else {
		vname := b.Varname()
		if b.Convert {
			vname = tobaseConvert(b)
		}
		value, err := baseMaxSizeExpr(b.Value, vname, b.BaseName(), b.TypeName(), b.common.AllocBound())
		if err != nil {
			s.p.printf("\npanic(\"Unable to determine max size: %s\")", err)
			s.state = add // reset the add to prevent further + expressions from being added to the end the panic statement
			return
		}
		s.addConstant(value)
	}
}

func baseMaxSizeExpr(value Primitive, vname, basename, typename string, allocbound string) (string, error) {
	if typename == "msgp.Raw" {
		return "", fmt.Errorf("MaxSize() not implemented for Raw type")
	}
	switch value {
	case Ext:
		return "", fmt.Errorf("MaxSize() not implemented for Ext type")
	case Intf:
		return "msgp.GuessSize(" + vname + ")", nil
	case IDENT:
		return getMaxSizeMethod(typename), nil
	case Bytes:
		if allocbound == "" || allocbound == "-" {
			return "", fmt.Errorf("Byteslice type %s is unbounded", vname)
		}
		return "msgp.BytesPrefixSize + " + allocbound, nil
	case String:
		if allocbound == "" || allocbound == "-" {
			return "", fmt.Errorf("String type %s is unbounded", vname)
		}
		return "msgp.StringPrefixSize +  " + allocbound, nil
	default:
		return builtinSize(basename), nil
	}
}

// return a fixed-size expression, if possible.
// only possible for *BaseElem, *Array and Struct.
// returns (expr, err)
func fixedMaxSizeExpr(e Elem) (string, error) {
	switch e := e.(type) {
	case *Array:
		if str, err := fixedMaxSizeExpr(e.Els); err == nil {
			return fmt.Sprintf("(%s * (%s))", e.Size, str), nil
		} else {
			return "", err
		}
	case *BaseElem:
		if fixedSize(e.Value) {
			return builtinSize(e.BaseName()), nil
		} else if (e.TypeName()) == "msgp.Raw" {
			return "", fmt.Errorf("Raw type is unbounded")
		} else if (e.Value) == String {
			if e.AllocBound() == "" || e.AllocBound() == "-" {
				return "", fmt.Errorf("String type is unbounded for %s", e.Varname())
			}
			return fmt.Sprintf("(msgp.StringPrefixSize + %s)", e.AllocBound()), nil
		} else if (e.Value) == IDENT {
			return fmt.Sprintf("(%s)", getMaxSizeMethod(e.TypeName())), nil
		} else if (e.Value) == Bytes {
			if e.AllocBound() == "" || e.AllocBound() == "-" {
				return "", fmt.Errorf("Inner byteslice type is unbounded")
			}
			return fmt.Sprintf("(msgp.BytesPrefixSize + %s)", e.AllocBound()), nil
		}
	case *Struct:
		return fmt.Sprintf("(%s)", getMaxSizeMethod(e.TypeName())), nil
	case *Slice:
		if e.AllocBound() == "" || e.AllocBound() == "-" {
			return "", fmt.Errorf("Slice %s is unbounded", e.Varname())
		}
		if str, err := fixedMaxSizeExpr(e.Els); err == nil {
			return fmt.Sprintf("(%s * (%s))", e.AllocBound(), str), nil
		} else {
			return "", err
		}
	}
	return fmt.Sprintf("%s, %s", e.TypeName(), reflect.TypeOf(e)), nil
}

func getMaxSizeMethod(typeName string) (s string) {
	var pos int
	dotIndex := strings.Index(typeName, ".")
	if dotIndex != -1 {
		pos = dotIndex + 1
	}
	b := []byte(typeName)
	b[pos] = bytes.ToUpper(b)[pos]
	return string(b) + "MaxSize()"
}
