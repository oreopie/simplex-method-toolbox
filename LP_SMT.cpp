/* 
*| SIMPLEX METHOD TOOLBOX V1.3
*| Copyright (c) 2017. All rights reserved.
*| Author: Shijie Jiang, shijie.jiang@hotmail.com
*| Affiliation: National University of Singapore (NUS)
*/
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <cmath>
#include <limits>
#include <iomanip>
#include <algorithm> // for std::find
#include <iterator> // for std::begin, std::end
using namespace std;

#define VMAX 1000 // Set the default maximum number of variables
#define CMAX 1000 // Set the default maximum number of constrains
#define IMAX 100 // Set the default maximum number of iterations
#define EPSILON 1E-8 // Set the error tolerance

int NV, NC, NV0, OPTIMAL;
// NV: number of variables 
// NC: number of constrains 
// NV0: original number of variables
// OPTIMAL: the state of finding optimum solution
double A[CMAX][VMAX], b[CMAX][1], C[VMAX], V[VMAX], CTemp[VMAX], ATemp[CMAX][VMAX];
// A[][],b[][1]: A and b in the constrains Ax=b 
// C[]: C in the objective function z=Cx
// V[]: signs of variables (whether nonnegative, nonpositive, or unrestricted)
// CTemp[], ATemp[][]: temporary C[] and A[][] for transfer
int NN[VMAX], NP[VMAX], UR[VMAX];
// NN[]: record the index of variables which belongs to nonnegative variables
// NP[]: record the index of variables which belongs to nonpositive variables
// UR[]: record the index of variables which belongs to unrestricted variables
int BASIC[VMAX], LB[IMAX], EB[IMAX];
// BASIC[]: record the index of variables which belongs to BFS
// LB[]: record the index of variables which leave the basis
// EB[]: record the index of variables which enter the basis
int CONSYMBOL[CMAX][1]; 
// CONSYMBOL[][1]: inequality or equality in each constraint (<=, >=, or =)
int NVNN, NVNP, NVUR;
// NVNN: number of nonnegative variables 
// NVNP: number of nonpositive variables 
// NVUR: number of unrestricted variables
int PI, PJ;
// PI: the row index of pivot 
// PJ: the column index of pivot
int COUNT, STATE; 
// COUNT: count of iteration in simplex method 
// STATE: the indicator of Phase I or Phase II
double Z = 0; 
// Z: objective value
double CSIGN; 
// CSIGN: control the sign of objective function based on the problem aim (min/max)

void CopyRightInfo(){
	cout << "\n**********************************************************************";
	cout << "\n**                 SIMPLEX METHOD TOOLBOX V1.3                      **";
	cout << "\n**  THIS IS DEVELOPED BY SHIJIE JIANG (SHIJIE.JIANG@HOTMAIL.COM)    **";
	cout << "\n**             COPYRIGHT (C) 2017  ALL RIGHTS RESERVED              **";
	cout << "\n**                    BUILT BY C++ ON 15/OCT/2017                   **";
	cout << "\n**                                                                  **";
	cout << "\n** *** Features (updated on 21/OCT/2017):                           **";
	cout << "\n** 1) Support MAX / MIN objective function, Equality and Inequality **";
	cout << "\n**    constraints, and Nonnegative / Nonpositive / Unrestricted     **";
	cout << "\n**    variables;                                                    **";
	cout << "\n** 2) Utilize Two-phase method;                                     **";
	cout << "\n** 3) Support both manually inputting or automatically importing;   **";
	cout << "\n** *** NEW Features (updated on 11/NOV/2017):                       **";
	cout << "\n** 1) Avoid artificial variables being basic (at ZERO level) at the **";
	cout << "\n**    end of Phase I.                                               **";
	cout << "\n** 2) Handle both infeasible solution and unbounded solution.       **";
	cout << "\n**                                                                  **";
	cout << "\n** More information please refer to User's Manual.                  **";
	cout << "\n**********************************************************************";
	cout << "\nPress Enter to Continue...";
	cin.ignore(numeric_limits<streamsize>::max(),'\n');
} // Print the copyright information

void DataInput(){
	int AIM,INEQUALITY; 
	// AIM: indicator of whether the LP is Min or Max 
	// INEQUALITY: indicator of whether the constrain is >=, <=, or =
	int I,J,K;
	bool EXISTS; 
	// EXISTS: indicator of whether nonnegative, nonpositive, or unrestricted variables exist
	double CVALUE; 
	// CVALUE: original input coefficients in objective function
	char OFCON, VCON, CCON; 
	// OFCON, VCON, CCON: indicators of the input confirmation of Objective Function, Variable signs, Constrains
	
	DefineObjective:{  // Define the objective fuction, either MIN or MAX will be transformed to MAX problem
		cout << "\n#####################################################################";
		cout << "\n######          STEP 1.1: DEFINE THE OBJECTIVE FUNCTION        ######";
		cout << "\n#####################################################################";
		cout << "\n#S1.1# Objective function is MAX(1) or MIN(2) ? "; 
		cout << "\n#S1.1# Please input 1 or 2:  "; cin  >> AIM;
		while ((AIM != 1) && (AIM != 2)) {
			cout << "\n ERROE MESSAGE : Input error! Unable to read...";
			cout << "\n#S1.1# Please input 1 or 2 ONLY:  ";
		  	cin.clear();
		  	cin.ignore(10000,'\n'); 
			cin  >> AIM;
		} // Input validation

		if (AIM == 1 )
			CSIGN = 1.0;
		else
			CSIGN = -1.0;

		cout << "#S1.1# Number of variables ? (please input an INTEGRE)  "; cin  >> NV;
		while (cin.fail()) {
			cerr << "\n###### ERROE MESSAGE : Input error! Unable to read...";
			cout << "\n#S1.1# Please input an integer ONLY:  ";
			cin.clear();
		  	cin.ignore(10000,'\n');
			cin  >> NV;
		} // Input validation
	
		cout << "#S1.1# Please input the coefficient of each variable:\n";
		for (J = 1; J <= NV; J++) {
			cout << " >>>>   X" <<J <<"? "; cin >> CVALUE;
			C[J] = CSIGN * CVALUE;  
		}

		cout << "#S1.1# Your objective function inputted is equivalent to: \n";
		cout << "        MAX Z = ";
		for (J = 1; J <= NV-1; J++) {
			cout << "(" << C[J] << ")X" << J <<" + ";
		}
		cout << "(" << C[J] << ")X" << J << endl;
	}

	cout << "#S1.1# Confirm? (Y/N)   "; cin >> OFCON;
	if (OFCON=='N' || OFCON=='n')
		goto DefineObjective;
	else
		cout << "#S1.1# Your objective function is confirmed.\n";

	DefineVariables:{  // Define the variable sign
		NVNN = 0; NVNP = 0; NVUR = 0; // initialize the number of nonnegative, nonpositive, and unrestricted variables.
		cout << "\n#####################################################################";
		cout << "\n######           STEP 1.2: DEFINE THE VARIABLE SIGN            ######";
		cout << "\n#####################################################################";
		cout << "\n#S1.2# Please indicate whether the constraint of each variable is: ";
		cout << "\n#S1.2# NONNEGATIVE(1), NONPOSITIVE(2), or UNRESTRICTED(3).\n";
		for (J = 1; J<=NV; J++) {
			cout << " >>>>   X" <<J <<"? "; cin >> V[J];
		}
		cout << "#S1.2# Your nonnegative variable(s) include: \n"; // Print the list of nonnegative variable(s) 
		cout << "        ";
		EXISTS = std::find(std::begin(V), std::end(V), 1) != std::end(V);
		if (!EXISTS) cout << "NONE";
		K = 1;
		for (J = 1; J<=NV; J++) {
			if (V[J] == 1) {
				cout << "X" <<J <<" ";
				NVNN = NVNN + 1;
				NN[K] = J;
				K = K+1;
			}
		}
		cout << "\n#S1.2# Your nonpositive variable(s) include: \n"; // Print the list of nonpositive variable(s) 
		cout << "        ";
		EXISTS = std::find(std::begin(V), std::end(V), 2) != std::end(V);
		if (!EXISTS) cout << "NONE";
		K = 1;
		for (J = 1; J<=NV; J++) {
			if (V[J] == 2) {
				cout << "X" <<J <<" ";
				NVNP = NVNP + 1;
				NP[K] = J;
				K = K+1;
			}
		}
		cout << "\n#S1.2# Your unrestricted variable(s) include: \n"; // Print the list of unrestricted variable(s) 
		cout << "        ";
		EXISTS = std::find(std::begin(V), std::end(V), 3) != std::end(V);
		if (!EXISTS) cout << "NONE";
		K = 1;
		for (J = 1; J<=NV; J++) {
			if (V[J] == 3) {
				cout << "X" <<J <<" ";
				NVUR = NVUR + 1;
				UR[K] = J;
				K = K+1;
			}
		}
	}
	cout << "\n#S1.2# Confirm? (Y/N)   "; cin >> VCON;
	if (VCON=='N' || VCON=='n')
		goto DefineVariables;
	else
		cout << "#S1.2# Your variables' sign are confirmed.\n";

	DefineConstraints:{  // Define the constraints
		cout << "\n#####################################################################";
		cout << "\n###### STEP 1.3: DEFINE THE CONSTRAINTS (EXCLUDING VARIABLES)  ######";
		cout << "\n#####################################################################";
		cout << "\n#S1.3# Number of constraints EXCLUDING variable constraints defined ";
		cout << "\n       in STEP 1.2 ? (please input an INTEGRE:) "; cin  >> NC;
		
		while (cin.fail()) {
			cerr << "\n ERROE MESSAGE : Input error! Unable to read..." << endl;
			cout << "#S1.3# Please input an INTEGER ONLY:  ";
			cin.clear();
			  cin.ignore(10000,'\n');
			cin  >> NC;
		}
		for (I = 1; I<=NC; I++) {
			cout << "#S1.3# Coefficient of each variable in constraint NO." << I <<":\n";
			for (J = 1; J<=NV; J++) {
				cout << " >>>>   X" <<J <<"? "; cin >> A[I][J];
			} // Define the coefficients in each constraint 
			cout << "#S1.3# Inequality or equality (1:<= | 2:>= | 3:=) in constraint NO."<< I <<" (please input 1/2/3): \n >>>>   ";
			cin >> CONSYMBOL[I][1];
			while ((CONSYMBOL[I][1] != 1) && (CONSYMBOL[I][1] != 2) && (CONSYMBOL[I][1] != 3)) {
			cerr << " ERROE MESSAGE : Input error! Unable to read...";
			cout << "\n#S1.3# Please input 1 or 2 or 3 ONLY:  ";
		  	cin.clear();
		  	cin.ignore(10000,'\n'); 
			cin  >> CONSYMBOL[I][1];
		} // Define the inequality in each constraint 
			cout << "#S1.3# Right-hand side in constraint NO."<< I <<":\n >>>>   ";
			cin >> b[I][1];
		} // Define the right-hand side in each constraint 

		cout << "#S1.3# Your constraint(s) excluding variable constraint(s) are: \n";
		for (I = 1; I<=NC; I++) {
			cout << "       ";
			for (J = 1; J <= NV-1; J++) {
			cout << "(" << A[I][J] << ")X" << J <<" + ";			
			}
			cout << "(" << A[I][J] << ")X" << J;
			switch(CONSYMBOL[I][1]) {
				case 1: cout << " <= "; break;
				case 2: cout << " >= "; break;
				case 3: cout << " = "; break;
			}
			cout << b[I][1] <<"\n";
		}
	}
	cout << "#S1.3# Confirm? (Y/N)   "; cin >> CCON;
	if (CCON=='N' || CCON=='n')
		goto DefineConstraints;
	else
		cout << "#S1.3# Your constraint(s) are confirmed.\n";
}

void ImportProblem(){
	string FILENAME, HEAD, VS, OBJ, CONS; 
	// Some strings recoding the file name and contents
	int I,J,K;
	int AIM, INEQUALITY; 
	// AIM: indicator of whether the LP is Min or Max 
	// INEQUALITY: indicator of whether the constrain is >=, <=, or =
	double CVALUE; 
	// CVALUE: original input coefficients in objective function
	bool EXISTS; 
	// EXISTS: indicator of whether nonnegative, nonpositive, or unrestricted variables exist
	char ICON; 
	// ICON: indicators of the confirmation of Imported information

	cout << "\n###################################################################";
	cout << "\n######    STEP 1: IMPORT THE LP PROBLEM FROM AN ASCII FILE   ######";
	cout << "\n###################################################################";
	ICONFIRM: {
		IMPORTFILE: {
			cout << "\n##S1## Please enter the file name with full path and extension : ";
			cout << "\n >>>>  ";
			cin >> FILENAME;
		}
		ifstream in(FILENAME); 
	  	if(!in) {
	   		cout << "##S1## Cannot open input file.\n";
	   		goto IMPORTFILE;
	  	} // Check the validation of imported file
	  	
	    getline(in, HEAD);  // delim defaults to '\n'
	    istringstream iss1(HEAD); // Read the first line of imported file (NV NC AIM)
	    iss1 >> NV; iss1 >> NC; iss1 >> AIM;

		if (AIM == 1 )
			CSIGN = 1.0;
		else
			CSIGN = -1.0;

		getline(in, VS);  // delim defaults to '\n'
	    istringstream iss2(VS); // Read the second line of imported file (the sign of each variable -- V[])
	    for (J = 1; J<=NV; J++) {
	    	iss2 >> V[J];
	    }

	  	getline(in, OBJ);  // delim defaults to '\n'
	    istringstream iss3(OBJ); // Read the third line of imported file (the coefficients of objective function  -- C[])
	    for (J = 1; J<=NV; J++) {
	    	iss3 >> CVALUE;
	    	C[J] = CSIGN * CVALUE;
	    }

	    for (I = 1; I<=NC; I++) { // Read the remaining lines of imported file (constraints -- A[][], CONSYMBOL[][1], b[])
	    	getline(in, CONS); 
		    istringstream iss4(CONS);
		    for (J = 1; J<=NV; J++) {
		    	iss4 >> A[I][J];
		    }
		    iss4 >> CONSYMBOL[I][1];
		    iss4 >> b[I][1];
		    iss4.clear();
	    }
		in.close();

		cout << "##S1## Your LP problem imported is equivalent to: \n"; // Print the information imported, the same as DataInput()
		cout << "        MAX Z = ";
		for (J = 1; J <= NV-1; J++) {
			cout << "(" << C[J] << ")X" << J <<" + ";
		}
		cout << "(" << C[J] << ")X" << J <<"\n";   
		cout << "       s.t.\n";
			for (I = 1; I<=NC; I++) {
				cout << "       ";
				for (J = 1; J <= NV-1; J++) {
				cout << "(" << A[I][J] << ")X" << J <<" + ";			
				}
				cout << "(" << A[I][J] << ")X" << J;
				switch(CONSYMBOL[I][1]) {
					case 1: cout << " <= "; break;
					case 2: cout << " >= "; break;
					case 3: cout << " = "; break;
				}
				cout << b[I][1] <<"\n";
			}

		cout << "##S1## Your NONNEGATIVE variable(s) include: \n";
		cout << "        ";
		EXISTS = std::find(std::begin(V), std::end(V), 1) != std::end(V);
		if (!EXISTS) cout << "NONE";
		K = 1;
		for (J = 1; J<=NV; J++) {
			if (V[J] == 1) {
				cout << "X" <<J <<" ";
				NVNN = NVNN + 1;
				NN[K] = J;
				K = K+1;
			}
		}
		cout << "\n       Your NONPOSITIVE variable(s) include: \n";
		cout << "        ";
		EXISTS = std::find(std::begin(V), std::end(V), 2) != std::end(V);
		if (!EXISTS) cout << "NONE";
		K = 1;
		for (J = 1; J<=NV; J++) {
			if (V[J] == 2) {
				cout << "X" <<J <<" ";
				NVNP = NVNP + 1;
				NP[K] = J;
				K = K+1;
			}
		}
		cout << "\n       Your UNRESTRICTED variable(s) include: \n";
		cout << "        ";
		EXISTS = std::find(std::begin(V), std::end(V), 3) != std::end(V);
		if (!EXISTS) cout << "NONE";
		K = 1;
		for (J = 1; J<=NV; J++) {
			if (V[J] == 3) {
				cout << "X" <<J <<" ";
				NVUR = NVUR + 1;
				UR[K] = J;
				K = K+1;
			}
		}
	}

	cout << "\n##S1## Confirm? (Y/N)   "; cin >> ICON;
	if (ICON=='N' || ICON=='n')
		goto ICONFIRM;
	else
		cout << "##S1## Your LP problem is confirmed.\n";
}

int Find(int ARR[], int LENGTH, int SEEK){
    for (int I = 1; I <= LENGTH; I++)
    {
        if (ARR[I] == SEEK) return I;
    }
    return -1;
}

void Canonicalize(){
	int I,J,K;	
	// 1) Make all the variables nonnegative (dealing with nonpositive and unrestricted variables)
	// 2) Transform all the inequations into equations with nonnegative right-hand side
	// 3) Add one artificial variable for each constraint directly to build an canonical form

	cout << "\n###################################################################";
	cout << "\n######            STEP 2: PREPROCESS THE LP PROBLEM          ######";
	cout << "\n###################################################################";
	if (NVNP > 0){ // Make nonpositive variables nonnegative
		for (K = 1; K<=NVNP; K++) {
			C[NP[K]] = -1 * C[NP[K]];
		}
		for (I = 1; I<=NC; I++) {
			for (K = 1; K<=NVNP; K++) {
				A[I][NP[K]] = -1 * A[I][NP[K]];
			}
		}
	}
	if (NVUR > 0){ // Make unrestricted variables nonnegative by splitting these variables
		NV = NV + NVUR;
		for (K = 1; K<=NVUR; K++) {
			C[NV-NVUR+K] = -1 * C[UR[K]];
		}
		for (I = 1; I<=NC; I++) {
			K = 1;
			for (J = NV-NVUR+1; J<=NV; J++) {
				A[I][J] = -1 * A[I][UR[K]];
				K = K + 1;
			}
		}
	}

	for (I = 1; I<=NC; I++) {
		switch(CONSYMBOL[I][1]) {
			case 1: { // <= add a slack variable	
				if (b[I][1] < 0) {
					for (J = 1; J<=NV; J++) {
						A[I][J] = -1 * A[I][J];
						if (A[I][J] == -0) A[I][J] = 0;
					}
					b[I][1] = -1 * b[I][1];
				}
				NV = NV + 1;  C[NV] = 0; A[I][NV] = 1;
				cout << "\n##S2## The row #" << I << " is a (<=)-inequality, and it has been transformed";
				cout << "\n       to an equation by adding a SLACK variable."; 
				break;
			}

			case 2: { // >= subtract a surplus variable
				if (b[I][1] < 0) {
					for (J = 1; J<=NV; J++) {
						A[I][J] = -1 * A[I][J];
						if (A[I][J] == -0) A[I][J] = 0;
					}
					b[I][1] = -1 * b[I][1];
				}
				NV = NV + 1; C[NV] = 0; A[I][NV] = -1;
				cout << "\n##S2## The row #" << I << " is a (>=)-inequality, and it has been transformed";
				cout << "\n       to an equation by subtracting a SURPLUS variable.";
				break;
			}

			case 3: { //= Just transform negative right-hand side to nonnegative
				if (b[I][1] < 0) {
					for (J = 1; J<=NV; J++) {
						A[I][J] = -1 * A[I][J];
						if (A[I][J] == -0) A[I][J] = 0;
					}
					b[I][1] = -1 * b[I][1];
					cout << "\n##S2## The row #" << I << " has a negative right-hand side, and it has been";
					cout << "\n       transformed to nonnegative.";	
				}
				break;
			}
		}
	}

	NV = NV + NC; // Add one artificial variable for each constraint directly to build an canonical form
	for (I = 1; I <= NC; I++){
		for (J = NV-NC+1; J <= NV; J++){
			A[I][J] = 0;
		}
		A[I][NV-NC+I] = 1;
	}

	cout << "\n##S2## The canonical form of your LP problem is:"; //Print the canonicalized LP problem
	cout << "\n        MAX Z = ";
	for (J = 1; J <= NV-1; J++) {
		cout << "(" << C[J] << ")X" << J <<" + ";
	}
	cout << "(" << C[NV] << ")X" << J;
	cout << "\n        s.t.\n";
	for (I = 1; I<=NC; I++) {
		cout << "        ";
		for (J = 1; J <= NV-1; J++) {
		cout << "(" << A[I][J] << ")X" << J <<" + ";			
		}
		cout << "(" << A[I][J] << ")X" << J << " = " << b[I][1] <<"\n";
		}
	cout << "       ";
	for (J = 1; J <= NV-1; J++) {
		cout << " X" << J << "," ;			
	}
		cout << " X" << NV << " >= 0\n";
}

void InitialBFS(); // Find the initial BFS
void Simplex();
void RowOperation();
void FindPivot();
void PhaseI(){
	int I,J,K;
	double PivotChange; // PivotChange: the coefficient of pivot element
	cout << "\n###################################################################";
	cout << "\n######            STEP 3: TWO-PHASE METHOD: PHASE I          ######";
	cout << "\n###################################################################\n";
	COUNT = 1; // Initialize the count of iteration in simplex method which starts from 1
	OPTIMAL = 0; // The state of finding OPTIMAL is false.
	STATE = 1; // This is the FIRST phase

	for (J=1; J<= NV; J++){ // Use a temporary array to record the processed C[] 
		CTemp[J] = C[J];
	}
	// The following two loops make the coefficients of artificial variables to be ONE, while others ZERO
	// Minimize the sum of artificial variables
	for (J=1; J<= NV-NC; J++){ 
		C[J] = 0;
	}
	for (J = NV-NC+1; J <= NV; J++) {
		C[J] = 1;
	}

	// Artificial variables should be substituted out in the r-row. SEE Section 3.4.2 in (Taha, 2014)
	for (J=1; J<= NV; J++){
		for (I=1; I<=NC; I++){
			C[J] = C[J] - A[I][J];
		}
	}
	for (I=1; I<=NC; I++){
		Z = Z - b[I][1];
	}

	InitialBFS(); // Call InitialBFS() to Initialize the BFS
	Simplex(); // Call Simplex() to solve the Phase I

	if (fabs(Z) > EPSILON) { // If the optimum is greater than 0 in Phase I, there is no feasible solution
		cout << "##S3## OPPS! No Feasible Solution!\n";
		exit(EXIT_FAILURE);
	} 
	else {
		for (I=1; I<= NC; I++){ // Check the zero-level artificial variables at the end of Phase I
			if (BASIC[I] > NV-NC){
				LB[COUNT] = BASIC[I];
				for (J=1; J<= NV-NC+1; J++){
					if (A[I][J] != 0 && Find(BASIC,NC,J)) {
						EB[COUNT] = J; 
						BASIC[I] = J;	
						PivotChange = A[I][J];
						PI = I;
						PJ = J;
					}
				}
				for (J=1; J<= NV-NC; J++){
					A[I][J] = A[I][J] / PivotChange;
				}
			cout << "##S3## As artificial variables X" << LB[COUNT] <<" is at ZERO level,"<<endl;
			cout << "##S3## it should be replaced by a nonbasic variable with a nonzero coefficient.\n"<<endl;
			RowOperation();
			cout << endl;
			}
		}
		cout << "\n##S3## The artificial variables have completed their mission, now move to Phase II.\n";
	} 
	NV = NV - NC; // Discard the artificial variables
}

void PhaseII(){
	int I,J,K;
	cout << "\n###################################################################";
	cout << "\n######            STEP 4: TWO-PHASE METHOD: PHASE II         ######";
	cout << "\n###################################################################\n";
	COUNT = 1; // Initialize the count of iteration in simplex method which starts from 1
	OPTIMAL = 0; // The state of finding OPTIMAL is false.
	STATE = 2; // This is the SECOND phase

	for (J = 1; J <= NV; J++) { // Restore the original objective function
		C[J] = -1 * CTemp[J];
	}

	// The following loops are used for substituting out the basic variables with nonzero coefficients in the z-row
	for (I = 1; I <= NC; I++) {
		for (J = 1; J <= NV; J++) {
			ATemp[I][J] = A[I][J];
		}
	}
	for (I = 1; I <= NC; I++) {
		for (J = 1; J <= NV; J++) {
			if (CTemp[BASIC[I]] == 0) goto e00;
			ATemp[I][J] = CTemp[BASIC[I]] * A[I][J];
			e00: ;
		}
	}
	for (I=1; I<=NC; I++){
		Z = Z - CTemp[BASIC[I]] * b[I][1];
	}
	for (J=1; J<= NV; J++){
		for (I=1; I<=NC; I++){
			if (CTemp[BASIC[I]] == 0) goto e10;
			C[J] = C[J] +  ATemp[I][J];
			e10: ;
		}
	}
	
	Simplex();
}

void InitialBFS(){ // Find the initial BFS
	int J, K;
	K = 1;
	// The initial BFS is the last NC variables (i.e., artificial variables) as we have added one artificial variable for each constraint
	for (J = NV-NC+1; J <= NV; J++) {
 		BASIC[K] = J;
		K++;
	}
}

void FindPivot() { // Find the pivot
	double CVMAX, RMAX, R; // R: the ratio of right-hand side to the corresponding positive constraint coefficient
	int I,J;
	CVMAX = 0.0; // Used to find the most negative C[]
	RMAX = 99999999.0; // Used to find the minimum R
	OPTIMAL = 0; // Set the state of finding optimum solution

	for(J = 1; J <= NV; J++) { // To find the column index of pivot
		if (C[J] < 0.0 && C[J] < CVMAX) {
			CVMAX = C[J];
			PJ = J;
		}
	}
	for (I=1; I<=NC; I++) { // To find the row index of pivot
		if (A[I][PJ]<=0.0) goto skip1; // The constraint coefficient should be strictly positive when calculating the ratio 
		R = fabs(b[I][1] / A[I][PJ]);
		if (R < RMAX) {
			RMAX = R;
			PI = I;
		}
		skip1: ;
	}
	cout << endl;

	LB[COUNT] = BASIC[PI]; // Record the index of variable which should leave the basis
	EB[COUNT] = PJ; // Record the index of variable which should enter the basis
	BASIC[PI] = PJ; // Change the basis
}

void RowOperation() {
	int I,J;

	for (J = 1; J <= NV; J++) { // Process A[pivot row][] except the pivot
		if (J == PJ) goto e30;
		A[PI][J] = A[PI][J] / A[PI][PJ];
		e30:;
	}
	b[PI][1] = b[PI][1] / A[PI][PJ]; // Process b[pivot row][1]
	
	// The following is due to the different aims of phase I and phase II
	if (STATE == 1) Z = Z - C[PJ] * b[PI][1];
	if (STATE == 2) Z = Z + C[PJ] * b[PI][1];

	A[PI][PJ] = A[PI][PJ] / A[PI][PJ]; // Make the pivot to be one.
	
	for (J = 1; J <= NV; J++) { // Process C[] except the pivot column
		if (J == PJ) goto e90;
		C[J] = C[J] - C[PJ] * A[PI][J];
		e90: ;
	}
	C[PJ] = C[PJ] - C[PJ] * A[PI][PJ]; // process C[pivot column] 

	for (I = 1; I <= NC; I++) { // Process b[][1] except the pivot row
		if (I == PI) goto e50;
		b[I][1] = b[I][1] - b[PI][1] * A[I][PJ];

		for (J = 1; J <= NV; J++) { // Process A[][] except the pivot row and pivot column
			if (J == PJ) goto e70;
			A[I][J] = A[I][J] - A[I][PJ] * A[PI][J];
			e70: ;			
		}
		e50: ;
	}

	for (I = 1; I <= NC; I++) { // Process A[][pivot column] except the pivot row
		if (I == PI) goto e60;
		A[I][PJ] = A[I][PJ] - A[I][PJ] * A[PI][PJ];
		e60: ;
	}

	cout << " ITERATION #"<< COUNT <<" : ";
	cout << " (X" << LB[COUNT] << " Leaves and X"<< EB[COUNT]  <<" Enters) \n";
	COUNT++; 
	cout << " BV";
	for (J = 1; J <= NV; J++) {
		cout << setw(8) << "X" << J << " ";	
	}
	cout << setw(9) << " CV";	
	cout << endl;
	cout << " ";
	for (J = 1; J <= NV+1; J++) {
		cout << "-----------";	
	}
	cout << endl;

	for (I = 1; I <= NC; I++) {
		cout << " X" << BASIC[I];
		for (J = 1; J <= NV; J++) {
		cout << setw(9) << A[I][J] << " ";
		}
		cout << setw(9) << b[I][1] << endl;
	}

	cout << " -Z";
	for (J = 1; J <= NV; J++) {
		cout << setw(9) << C[J] << " ";
	}
	cout << setw(9) << Z << endl;
}

void Optimal() {
	int I,J;
	OPTIMAL = 0;
	bool SUBEXIT[VMAX], EXIT = 1; // Control to check whether C[] are positive or zero
	for(J = 1; J <= NV; J++) { // If all the C[] are positive or zero, we find the optimum solution
		SUBEXIT[J] = 0;
		if (C[J] >= 0.0) SUBEXIT[J] = 1;
		else SUBEXIT[J] = 0;
		EXIT = EXIT && SUBEXIT[J];
	}
	if (EXIT) OPTIMAL = 1;
	if (LB[COUNT-2]==EB[COUNT-1] && LB[COUNT-1]==EB[COUNT-2]) OPTIMAL = -1; 
	// If the entering variable and leaving variable appear alternately and endlessly, then the objective value is unbounded.
}

void Simplex() {
	int I,J;
	// Print the Head Information
	cout << " ITERATION #"<< COUNT <<": \n"; COUNT++; 
	cout << " BV";
	for (J = 1; J <= NV; J++) {
		cout << setw(8) << "X" << J << " ";	
	}
	cout << setw(9) << " CV";	
	cout << endl;
	cout << " ";
	for (J = 1; J <= NV+1; J++) {
		cout << "-----------";	
	}
	cout << endl;

	// Print the x-row(s) Information
	for (I = 1; I <= NC; I++) {
		cout << " X" << BASIC[I];
		for (J = 1; J <= NV; J++) {
		cout << setw(9) << A[I][J] << " ";
		}
		cout << setw(9) << b[I][1] << endl;
	}

	// Print the z-row Information
	cout << " -Z";
	for (J = 1; J <= NV; J++) {
		cout << setw(9) << C[J] << " ";
	}
	cout << setw(9) << Z << endl;

	e10: FindPivot(); 
	RowOperation(); // Perform Gauss-Jordan Row Operation
	Optimal();

	if (OPTIMAL == 0) goto e10; // If not find the optimum solution, then goto e10 to continue
	if (OPTIMAL == -1){ // If objective function is unbounded, then exit
		cout << "\n**********************************************************************\n";
		cout << "****** OPPS! Unbounded Objective Value!\n";
		exit(EXIT_FAILURE);
	} 
}

void ShowResults() {
	int I,J,K;
	double OX[NV0]; // OX: the final values restored on the original X

	for (J = 1; J <= NV0; J++) {
		OX[J] = 0;
		for (I=1; I<= NC; I++){
			if (BASIC[I] == J) {
				OX[J] = b[I][1];
			}
		}
	}
	if (NVNP > 0){
		for (J = 1; J <= NV0; J++) {
			for (K = 1; K<=NVNP; K++) {				
				if (NP[K] == J)
					OX[J] = - b[NP[K-1]][1];
			}
		}
	}
	if (NVUR > 0){
		for (J = 1; J <= NV0; J++) {
			for (K = 1; K<=NVUR; K++) {
				if (UR[K] == J)
					OX[J] = OX[J] - b[Find(BASIC,NC,UR[K]+NVNP+NV0-1)][1];
			}

		}
	}
	for (J = 1; J <= NV0; J++) {
		if (OX[J]==-0) OX[J] = 0;
	}

	cout << "\n****** The optimal variable(s) of your original problem are:";
	for (J = 1; J <= NV0; J++) {
		cout << "\n       | X" << J << " "<< OX[J];
	}
	cout << "\n****** The optimum of your original problem is : " << (-1) * CSIGN * Z << endl;
	cout << endl;
}


int main() {
	int METHOD;
	CopyRightInfo();
	cout << "\n****** Please choose a method to define the LP problem: ";
	cout << "\n****** 1 -- Import from an ASCII file";
	cout << "\n****** 2 -- Input manually step by step";
	cout << "\n >>>>  ";
	cin >> METHOD;
	
	while ((METHOD != 1) && (METHOD != 2)) {
		cerr << "\n ERROE MESSAGE : Input error! Unable to read...";
		cout << "\n****** Please input 1 or 2 ONLY:  ";
		  cin.clear();
		  cin.ignore(10000,'\n'); 
		cin  >> METHOD;
	}
	if (METHOD == 1) 
		ImportProblem();
	else 
		DataInput();
	
	NV0 = NV;
	Canonicalize();
	PhaseI();
	PhaseII();
	ShowResults();
	cout << "\nPress Enter to Exit...";
    cin.ignore().get(); //Pause Command 
  	return 0;
}
