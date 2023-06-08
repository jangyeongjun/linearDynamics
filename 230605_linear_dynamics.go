package main

import (
	"fmt"
	"math"
	"os"

	// "math/rand"
	"reflect"

	"github.com/tuneinsight/lattigo/v4/rgsw"
	"github.com/tuneinsight/lattigo/v4/ring"
	"github.com/tuneinsight/lattigo/v4/rlwe"
	"github.com/tuneinsight/lattigo/v4/rlwe/ringqp"

	"gonum.org/v1/plot"
	"gonum.org/v1/plot/plotter"

	// "gonum.org/v1/plot/plotutil"
	"gonum.org/v1/plot/vg"
	"gonum.org/v1/plot/vg/draw"
	"gonum.org/v1/plot/vg/vgimg"
)

func modZq(a [][]float64, params rlwe.Parameters, factor float64) [][]float64 {
	q := factor
	b := make([][]float64, len(a))
	for i := range a {
		b[i] = make([]float64, len(a[0]))
	}

	for i := 0; i < len(a); i++ {
		for j := 0; j < len(a[0]); j++ {
			b[i][j] = a[i][j] - math.Floor(a[i][j]/q)*q
		}
	}
	return b
}

func addMod(ctTmp [][]*rlwe.Ciphertext, ctA [][]*rlwe.Ciphertext, params rlwe.Parameters) {
	// ctTmp : m x n
	// ctA : m x 1
	for i := 0; i < len(ctTmp); i++ {
		ttmp0 := ring.NewPoly(params.N(), params.MaxLevel())
		ttmp1 := ring.NewPoly(params.N(), params.MaxLevel())

		for j := 0; j < len(ctTmp[0]); j++ {
			params.RingQ().Add(ctTmp[i][j].Value[0], ttmp0, ttmp0)
			params.RingQ().Mod(ttmp0, params.Q()[0], ttmp0)
			params.RingQ().Add(ctTmp[i][j].Value[1], ttmp1, ttmp1)
			params.RingQ().Mod(ttmp1, params.Q()[0], ttmp1)
		}
		ctA[i][0].Value[0] = ttmp0
		ctA[i][0].Value[1] = ttmp1
	}
}

func externalProduct(ctA [][]*rlwe.Ciphertext, ctB [][]*rgsw.Ciphertext, evaluator *rgsw.Evaluator) [][]*rlwe.Ciphertext {
	// A: m x l  1 x 1
	// B: n x m  2 x 1

	ctTmp := rlweCtCopy(len(ctB), len(ctB[0]), ctA) // 2x1

	ctOut := rlweCtCopy(len(ctB), len(ctA[0]), ctA) // 2x1

	for i := 0; i < len(ctB); i++ {
		for j := 0; j < len(ctB[0]); j++ {
			evaluator.ExternalProduct(ctA[j][0], ctB[i][j], ctTmp[i][j])
		}
	}

	addMod(ctTmp, ctOut, evaluator.Parameters())
	return ctOut
}

func encodeRlwe(A [][]float64, ptA [][]*rlwe.Plaintext, scale float64, params rlwe.Parameters, factor float64) {
	B := modZq(A, params, factor)

	for i := range A {
		for j := range A[0] {
			for k := 0; k < params.N(); k++ {
				ptA[i][j].Value.Coeffs[0][k] = uint64(B[i][j] * scale)
			}
		}
	}
}

func encodeRgsw(A [][]float64, ptA [][]*rlwe.Plaintext, params rlwe.Parameters) {
	B := modZq(A, params, float64(params.Q()[0]))

	for i := range A {
		for j := range A[0] {
			for k := 0; k < params.N(); k++ {
				ptA[i][j].Value.Coeffs[0][k] = uint64(B[i][j])
			}
		}
	}
}

func encryptRlwe(ptA [][]*rlwe.Plaintext, encryptor rlwe.Encryptor) [][]*rlwe.Ciphertext {
	ctxPlant := make([][]*rlwe.Ciphertext, len(ptA))
	for i := range ctxPlant {
		ctxPlant[i] = make([]*rlwe.Ciphertext, len(ptA[0]))
	}

	for i := range ptA {
		for j := range ptA[0] {
			ctxPlant[i][j] = encryptor.EncryptNew(ptA[i][j])
		}
	}
	return ctxPlant
}

func encryptRgsw(ptA [][]*rlwe.Plaintext, ctA [][]*rgsw.Ciphertext, encryptor *rgsw.Encryptor) {
	for i := range ptA {
		for j := range ptA[0] {
			encryptor.Encrypt(ptA[i][j], ctA[i][j])
		}
	}
}

func decodeRlwe(ptA [][]*rlwe.Plaintext, scale float64, params rlwe.Parameters, factor float64) [][]float64 {
	for i := 0; i < len(ptA); i++ {
		if ptA[i][0].IsNTT {
			params.RingQ().InvNTT(ptA[i][0].Value, ptA[i][0].Value)
		}
	}
	// q := float64(params.Q()[0])
	q := factor
	valA := make([][]float64, len(ptA))
	for i := range ptA {
		valA[i] = make([]float64, len(ptA[0]))
	}

	for i := range valA {
		for j := range valA[0] {
			valA[i][j] = float64(ptA[i][j].Value.Coeffs[0][0]) / scale
			valA[i][j] = (valA[i][j] - math.Floor((valA[i][j]+q/2.0)/q)*q)
		}
	}
	return valA
}

func decryptRlwe(ctA [][]*rlwe.Ciphertext, decryptor rlwe.Decryptor) [][]*rlwe.Plaintext {
	ptA := make([][]*rlwe.Plaintext, len(ctA))
	for i := range ptA {
		ptA[i] = make([]*rlwe.Plaintext, len(ctA[0]))
	}
	for i := range ptA {
		for j := range ptA[0] {
			ptA[i][j] = decryptor.DecryptNew(ctA[i][j])
		}
	}
	return ptA
}

func rlwePt(row int, col int, params rlwe.Parameters) [][]*rlwe.Plaintext {
	// return m by n matrix
	mat := make([][]*rlwe.Plaintext, row)
	for i := range mat {
		mat[i] = make([]*rlwe.Plaintext, col)
	}

	for i := 0; i < row; i++ {
		for j := 0; j < col; j++ {
			mat[i][j] = rlwe.NewPlaintext(params, params.MaxLevel())
		}
	}
	return mat
}

func rlweCtCopy(row int, col int, ctA [][]*rlwe.Ciphertext) [][]*rlwe.Ciphertext {
	ctTmp := make([][]*rlwe.Ciphertext, row)
	for i := range ctTmp {
		ctTmp[i] = make([]*rlwe.Ciphertext, col)
	}
	for i := range ctTmp {
		for j := range ctTmp[0] {
			ctTmp[i][j] = ctA[0][0].CopyNew()
		}
	}
	return ctTmp
}

func rgswCt(row int, col int, levelQ int, levelP int, decompRNS int, decompPw2 int, ringQP *ringqp.Ring) [][]*rgsw.Ciphertext {
	// return m by n matrix
	mat := make([][]*rgsw.Ciphertext, row)
	for i := range mat {
		mat[i] = make([]*rgsw.Ciphertext, col)
	}

	for i := 0; i < row; i++ {
		for j := 0; j < col; j++ {
			mat[i][j] = rgsw.NewCiphertext(levelQ, levelP, decompRNS, decompPw2, *ringQP)
		}
	}
	return mat
}

func matMult(A [][]float64, B [][]float64) [][]float64 {
	// A : m x n
	// B : n x l
	m := len(A)
	n := len(A[0])
	n1 := len(B)
	l := len(B[0])

	if n != n1 {
		panic(fmt.Errorf("Matrix dimension don't match"))
	}

	C := make([][]float64, m)
	for i := 0; i < m; i++ {
		C[i] = make([]float64, l)
	}

	for i := 0; i < m; i++ {
		for j := 0; j < l; j++ {
			tmp := 0.0
			for k := 0; k < n; k++ {
				tmp = tmp + A[i][k]*B[k][j]
			}
			C[i][j] = tmp
		}
	}
	return C
}

func matAdd(A [][]float64, B [][]float64) [][]float64 {
	// A : m x n
	// B : m x n
	m := len(A)
	n := len(A[0])

	C := make([][]float64, m)
	for i := 0; i < m; i++ {
		C[i] = make([]float64, n)
	}

	for i := 0; i < m; i++ {
		for j := 0; j < n; j++ {
			C[i][j] = A[i][j] + B[i][j]
		}
	}
	return C
}

func ctAdd(ctA [][]*rlwe.Ciphertext, ctB [][]*rlwe.Ciphertext, params rlwe.Parameters) [][]*rlwe.Ciphertext {
	// A : m x n
	// B : m x n
	m := len(ctA)
	n := len(ctA[0])
	ctC := rlweCtCopy(m, n, ctA)

	for i := 0; i < m; i++ {
		for j := 0; j < n; j++ {
			params.RingQ().Add(ctA[i][j].Value[0], ctB[i][j].Value[0], ctC[i][j].Value[0])
			params.RingQ().Mod(ctC[i][j].Value[0], params.Q()[0], ctC[i][j].Value[0])
			params.RingQ().Add(ctA[i][j].Value[1], ctB[i][j].Value[1], ctC[i][j].Value[1])
			params.RingQ().Mod(ctC[i][j].Value[1], params.Q()[0], ctC[i][j].Value[1])
		}
	}
	return ctC
}

func main() {
	params, _ := rlwe.NewParametersFromLiteral(rlwe.ParametersLiteral{
		LogN: 10,
		// LogQ:           []int{27},
		LogQ:           []int{42},
		Pow2Base:       7,
		DefaultNTTFlag: true,
	})

	kgen := rlwe.NewKeyGenerator(params)

	sk := kgen.GenSecretKey()
	rlk := kgen.GenRelinearizationKey(sk, 1)
	evk := &rlwe.EvaluationKey{Rlk: rlk}

	encryptorRLWE := rlwe.NewEncryptor(params, sk)
	decryptorRLWE := rlwe.NewDecryptor(params, sk)
	encryptorRGSW := rgsw.NewEncryptor(params, sk)
	evaluator := rgsw.NewEvaluator(params, evk)

	levelQ := params.QCount() - 1
	levelP := params.PCount() - 1
	decompRNS := params.DecompRNS(levelQ, levelP)
	decompPw2 := params.DecompPw2(levelQ, levelP)
	ringQP := params.RingQP()

	// ================================
	factor := 32.0
	scale := float64(params.Q()[0]) / factor
	iter := 15
	// ================================

	fmt.Println(reflect.TypeOf(ringQP))

	// ============================================
	// Plant Define
	// x(t+1) = Ax(t)+Bu(t)
	// y(t) = Cx(t)

	// A: n_p x n_p
	// B: n_p x m
	// C: p   x n_p

	A := [][]float64{
		{-2.6828, -2.0000},
		{3.3885, -0.6429},
	}
	B := [][]float64{
		{3.6828},
		{-3.0393},
	}
	C := [][]float64{
		{-0.6508, -3.6429},
	}

	// ============================================
	// Controller Define
	// x_c(t+1) = Fx_c(t)+Gy(t)
	// y(t) = Hu(t)

	// F: n x n
	// G: n x p
	// H: m x n

	F := [][]float64{
		{1, -2},
		{1, 3},
	}

	G := [][]float64{
		{0},
		{1},
	}
	H := [][]float64{
		{1, 0},
	}

	// ============================================
	// Initial condition setting
	xPlantInit := [][]float64{
		{0.2},
		{0.1},
	}
	xContInit := [][]float64{
		{0.1},
		{0},
	}

	// =============================================
	// RGSW encryption
	n := len(F)
	p_ := len(G[0])
	m := len(H)

	ptF := rlwePt(n, n, params)
	ptG := rlwePt(n, p_, params)
	ptH := rlwePt(m, n, params)

	encodeRgsw(F, ptF, params)
	encodeRgsw(G, ptG, params)
	encodeRgsw(H, ptH, params)

	ctF := rgswCt(n, n, levelQ, levelP, decompRNS, decompPw2, ringQP)
	ctG := rgswCt(n, p_, levelQ, levelP, decompRNS, decompPw2, ringQP)
	ctH := rgswCt(m, n, levelQ, levelP, decompRNS, decompPw2, ringQP)

	encryptRgsw(ptF, ctF, encryptorRGSW)
	encryptRgsw(ptG, ctG, encryptorRGSW)
	encryptRgsw(ptH, ctH, encryptorRGSW)

	// =============================================
	// Unencrypted closed loop dynamics update
	fmt.Println("Nominal Loop Start")

	YOUT := []float64{}
	UOUT := []float64{}
	XCONT0 := []float64{}
	XCONT1 := []float64{}
	XPLANT0 := []float64{}
	XPLANT1 := []float64{}

	xPlantUnenc := xPlantInit
	xContUnenc := xContInit
	for i := 0; i < iter; i++ {
		// Output of the plant
		yOut := matMult(C, xPlantUnenc)

		// Output of the controller
		uOut := matMult(H, xContUnenc)

		// Plant update
		xPlantUnenc = matAdd(matMult(A, xPlantUnenc), matMult(B, uOut))

		// Controller update
		xContUnenc = matAdd(matMult(F, xContUnenc), matMult(G, yOut))

		// Decrypt
		fmt.Println("=======================")
		fmt.Printf("Plant output at iter %d: \n %v \n", i, yOut)
		fmt.Printf("Controller output at iter %d: \n %v \n", i, uOut)
		fmt.Printf("Plant state at iter %d: \n %v \n", i, xPlantUnenc)
		fmt.Printf("Controller state at iter %d: \n %v \n", i, xContUnenc)

		// Append data
		YOUT = append(YOUT, yOut[0][0])
		UOUT = append(UOUT, uOut[0][0])
		XCONT0 = append(XCONT0, xContUnenc[0][0])
		XCONT1 = append(XCONT1, xContUnenc[1][0])
		XPLANT0 = append(XPLANT0, xPlantUnenc[0][0])
		XPLANT1 = append(XPLANT1, xPlantUnenc[1][0])
	}

	// =============================================
	// Encrypted closed loop dynamics update
	xPlantEnc := xPlantInit
	xContEnc := xContInit

	ptxCont := rlwePt(n, 1, params)
	encodeRlwe(xContEnc, ptxCont, scale, params, factor)
	ctxCont := encryptRlwe(ptxCont, encryptorRLWE)

	fmt.Println("******************************")
	fmt.Println("Encrypted Loop Start")

	YOUTENC := []float64{}
	UOUTENC := []float64{}
	XCONT0ENC := []float64{}
	XCONT1ENC := []float64{}
	XPLANT0ENC := []float64{}
	XPLANT1ENC := []float64{}

	for i := 0; i < iter; i++ {
		// Output of the plant
		yOut := matMult(C, xPlantEnc)
		ptyOut := rlwePt(1, 1, params)
		encodeRlwe(yOut, ptyOut, scale, params, factor)
		ctyOut := encryptRlwe(ptyOut, encryptorRLWE)
		ptyOut = decryptRlwe(ctyOut, decryptorRLWE)
		valyOut := decodeRlwe(ptyOut, scale, params, factor)

		// Output of the controller
		ctExt := externalProduct(ctxCont, ctH, evaluator)
		ptExt := decryptRlwe(ctExt, decryptorRLWE)
		uOut := decodeRlwe(ptExt, scale, params, factor)

		// Plant update
		xPlantEnc = matAdd(matMult(A, xPlantEnc), matMult(B, uOut))

		// Controller update
		ctxCont = ctAdd(externalProduct(ctxCont, ctF, evaluator), externalProduct(ctyOut, ctG, evaluator), params)

		// Decrypt controller state
		ptCont := decryptRlwe(ctxCont, decryptorRLWE)
		valCont := decodeRlwe(ptCont, scale, params, factor)

		fmt.Println("=======================")
		fmt.Printf("Plant output at iter %d: \n %v \n", i, valyOut)
		fmt.Printf("Decrypted controller output at iter %d: \n %v \n", i, uOut)
		fmt.Printf("Plant state at iter %d: \n %v \n", i, xPlantEnc)
		fmt.Printf("Decrypted controller state at iter %d: \n %v \n", i, valCont)

		// Append data
		YOUTENC = append(YOUTENC, valyOut[0][0])
		UOUTENC = append(UOUTENC, uOut[0][0])
		XCONT0ENC = append(XCONT0ENC, valCont[0][0])
		XCONT1ENC = append(XCONT1ENC, valCont[1][0])
		XPLANT0ENC = append(XPLANT0ENC, xPlantEnc[0][0])
		XPLANT1ENC = append(XPLANT1ENC, xPlantEnc[1][0])
	}

	// **************************** Plot section *************************************
	const rows, cols = 2, 3

	// UNENCRYPTED CONTROLLER SUBPLOT
	plotsUnenc := make([][]*plot.Plot, rows)
	for i := 0; i < rows; i++ {
		plotsUnenc[i] = make([]*plot.Plot, cols)
		for j := 0; j < cols; j++ {
			p := plot.New()
			pts := make(plotter.XYs, iter)

			for k := range pts {
				pts[k].X = float64(k)
			}

			// First row
			if i == 0 {
				if j == 0 {
					for k := range pts {
						pts[k].Y = YOUT[k]

					}
					p.Title.Text = "Plant Output"
				} else if j == 1 {
					for k := range pts {
						pts[k].Y = UOUT[k]
					}
					p.Title.Text = "Controller Output"
				} else {
					for k := range pts {
						pts[k].Y = XCONT0[k]
					}
					p.Title.Text = "Controller State 1"
				}

			} else {

				// Second row
				if j == 0 {
					for k := range pts {
						pts[k].Y = XCONT1[k]

					}
					p.Title.Text = "Controller State 2"
				} else if j == 1 {
					for k := range pts {
						pts[k].Y = XPLANT0[k]
					}
					p.Title.Text = "Plant State 1"
				} else {
					for k := range pts {
						pts[k].Y = XPLANT1[k]
					}
					p.Title.Text = "Plant State 2"
				}
			}
			p.X.Label.Text = "X"
			p.Y.Label.Text = "Y"
			p.Y.Min = -4
			p.Y.Max = 4
			p.Add(plotter.NewGrid())
			lLine, lPoints, _ := plotter.NewLinePoints(pts)
			p.Add(lLine, lPoints)
			plotsUnenc[i][j] = p

		}
	}

	// ENCRYPTED CONTROLLER SUBPLOT
	plotsEnc := make([][]*plot.Plot, rows)
	for i := 0; i < rows; i++ {
		plotsEnc[i] = make([]*plot.Plot, cols)
		for j := 0; j < cols; j++ {
			p := plot.New()
			pts := make(plotter.XYs, iter)

			for k := range pts {
				pts[k].X = float64(k)
			}

			// First row
			if i == 0 {
				if j == 0 {
					for k := range pts {
						pts[k].Y = YOUTENC[k]

					}
					p.Title.Text = "Plant Output"
				} else if j == 1 {
					for k := range pts {
						pts[k].Y = UOUTENC[k]
					}
					p.Title.Text = "Controller Output"
				} else {
					for k := range pts {
						pts[k].Y = XCONT0ENC[k]
					}
					p.Title.Text = "Controller State 1"
				}

			} else {

				// Second row
				if j == 0 {
					for k := range pts {
						pts[k].Y = XCONT1ENC[k]

					}
					p.Title.Text = "Controller State 2"
				} else if j == 1 {
					for k := range pts {
						pts[k].Y = XPLANT0ENC[k]
					}
					p.Title.Text = "Plant State 1"
				} else {
					for k := range pts {
						pts[k].Y = XPLANT1ENC[k]
					}
					p.Title.Text = "Plant State 2"
				}
			}
			p.X.Label.Text = "X"
			p.Y.Label.Text = "Y"
			p.Y.Min = -4
			p.Y.Max = 4
			p.Add(plotter.NewGrid())
			lLine, lPoints, _ := plotter.NewLinePoints(pts)
			p.Add(lLine, lPoints)
			plotsEnc[i][j] = p

		}
	}

	// DIFFERENCE SUBPLOT
	plotsDiff := make([][]*plot.Plot, rows)
	for i := 0; i < rows; i++ {
		plotsDiff[i] = make([]*plot.Plot, cols)
		for j := 0; j < cols; j++ {
			p := plot.New()
			pts := make(plotter.XYs, iter)

			for k := range pts {
				pts[k].X = float64(k)
			}

			// First row
			if i == 0 {
				if j == 0 {
					for k := range pts {
						pts[k].Y = YOUT[k] - YOUTENC[k]

					}
					p.Title.Text = "Plant Output"
				} else if j == 1 {
					for k := range pts {
						pts[k].Y = UOUT[k] - UOUTENC[k]
					}
					p.Title.Text = "Controller Output"
				} else {
					for k := range pts {
						pts[k].Y = XCONT0[k] - XCONT0ENC[k]
					}
					p.Title.Text = "Controller State 1"
				}

			} else {

				// Second row
				if j == 0 {
					for k := range pts {
						pts[k].Y = XCONT1[k] - XCONT1ENC[k]

					}
					p.Title.Text = "Controller State 2"
				} else if j == 1 {
					for k := range pts {
						pts[k].Y = XPLANT0[k] - XPLANT0ENC[k]
					}
					p.Title.Text = "Plant State 1"
				} else {
					for k := range pts {
						pts[k].Y = XPLANT1[k] - XPLANT1ENC[k]
					}
					p.Title.Text = "Plant State 2"
				}
			}
			p.X.Label.Text = "X"
			p.Y.Label.Text = "Y"
			p.Y.Min = -1e-04
			p.Y.Max = 1e-04
			p.Add(plotter.NewGrid())
			lLine, lPoints, _ := plotter.NewLinePoints(pts)
			p.Add(lLine, lPoints)
			plotsDiff[i][j] = p

		}
	}

	imgUnenc := vgimg.New(vg.Points(1000), vg.Points(500))
	dcUnenc := draw.New(imgUnenc)
	imgEnc := vgimg.New(vg.Points(1000), vg.Points(500))
	dcEnc := draw.New(imgEnc)
	imgDiff := vgimg.New(vg.Points(1000), vg.Points(500))
	dcDiff := draw.New(imgDiff)
	t := draw.Tiles{
		Rows:      rows,
		Cols:      cols,
		PadX:      vg.Millimeter,
		PadY:      vg.Millimeter,
		PadTop:    vg.Points(50),
		PadBottom: vg.Points(50),
		PadLeft:   vg.Points(50),
		PadRight:  vg.Points(50),
	}

	canvasesUnenc := plot.Align(plotsUnenc, t, dcUnenc)
	canvasesEnc := plot.Align(plotsEnc, t, dcEnc)
	canvasesDiff := plot.Align(plotsDiff, t, dcDiff)
	for i := 0; i < rows; i++ {
		for j := 0; j < cols; j++ {
			if plotsUnenc[i][j] != nil {
				plotsUnenc[i][j].Draw(canvasesUnenc[i][j])
			}
			if plotsEnc[i][j] != nil {
				plotsEnc[i][j].Draw(canvasesEnc[i][j])
			}
			if plotsDiff[i][j] != nil {
				plotsDiff[i][j].Draw(canvasesDiff[i][j])
			}
		}
	}
	w, err := os.Create("Unencrypted.png")
	if err != nil {
		panic(err)
	}
	defer w.Close()
	png := vgimg.PngCanvas{Canvas: imgUnenc}
	if _, err := png.WriteTo(w); err != nil {
		panic(err)
	}

	w, err = os.Create("Encrypted.png")
	if err != nil {
		panic(err)
	}
	defer w.Close()
	png = vgimg.PngCanvas{Canvas: imgEnc}
	if _, err := png.WriteTo(w); err != nil {
		panic(err)
	}

	w, err = os.Create("Difference.png")
	if err != nil {
		panic(err)
	}
	defer w.Close()
	png = vgimg.PngCanvas{Canvas: imgDiff}
	if _, err := png.WriteTo(w); err != nil {
		panic(err)
	}
}
