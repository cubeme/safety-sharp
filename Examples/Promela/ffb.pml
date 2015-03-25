//-- SCALES -------------------------------------------------------------------------------------
#define DefPosScale 	3	// 1 unit represents PosScale meters
#define DefTimeScale 	2	// 1 unit represents TimeScale seconds
//-- SCALES -------------------------------------------------------------------------------------


//-- MISC PARAMETERS ----------------------------------------------------------------------------
#define DefSafetyMargin 	(200 / DefPosScale) 							//--here Arbitrarily 200m. In NuSmv 350m: 92m safety margin for odometer failure -1 and 258m technical margin -> 45m rounding errors + 174m 2 time steps delay + 39m discrete position modeling
#define DefCommDelay 		(2 / DefTimeScale)							//-- 2s
#define DefClosingDelay 	(60 / DefTimeScale)							//-- 60s
#define DefCloseTimeout 	(240 / DefTimeScale)							//-- 240s
#define DefMaxSpeed 		(44 * DefTimeScale / DefPosScale)				//-- 160km/h = 44m/s
#define DefDec 			(1 * DefTimeScale * DefTimeScale / DefPosScale)	//-- 1m/s^2 -> at 160km/h, the train stops after 0,97km
//-- MISC PARAMETERS ----------------------------------------------------------------------------

//-- POSITIONS ----------------------------------------------------------------------------------
//-- The train's position ranges from 0 to EndPos. We are not interested in the train's actual
//-- position if it falls outside that range.		
#define DefEndPos 		(10000 / DefPosScale)	//-- 10km
#define DefSensorPos 	(9300 / DefPosScale)	//-- 9,3km
#define DefCrossingPos (9000 / DefPosScale)	//-- 9km

#define DefVirtualSpeed 	(Speed + FailureOdometer > 0 -> Speed + FailureOdometer : 0)
#define DefStopPos 		(DefCrossingPos - DefVirtualSpeed * DefVirtualSpeed / (2 * DefDec) - DefSafetyMargin)
#define DefQueryPos 		(DefStopPos - 2 * DefCommDelay * DefVirtualSpeed - DefSafetyMargin)
#define DefClosePos 		(DefQueryPos - (DefCommDelay + DefClosingDelay) * DefVirtualSpeed - DefSafetyMargin)
//-- POSITIONS ----------------------------------------------------------------------------------



//-- MAGIC NUMBERS ------------------------------------------------------------------------------
//-- Timer
#define NoStateTimerClosingInactive 	1
#define NoStateTimerClosingSignal	 	2
#define NoStateTimerClosingActive	 	3

#define NoStateTimerOpenInactive 		1
#define NoStateTimerOpenSignal	 		2
#define NoStateTimerOpenActive	 		3


//-- Communication
#define NoStateCommCloseInactive 		1
#define NoStateCommCloseSignal 			2
#define NoStateCommCloseActive 			3

#define NoStateCommQueryInactive 		1
#define NoStateCommQuerySignal 			2
#define NoStateCommQueryActive 			3

#define NoStateCommSecuredInactive 		1
#define NoStateCommSecuredSignal 		2
#define NoStateCommSecuredActive 		3

				
//-- Components
#define NoStateCrossingOpened 			1
#define NoStateCrossingClosing 			2
#define NoStateCrossingClosed 			3
#define NoStateCrossingStuck			4

// mtype = {NoStateTrainIdle,NoStateTrainWait,NoStateTrainQuery,NoStateTrainStop,NoStateTrainGo};
#define NoStateTrainIdle 				1
#define NoStateTrainWait 				2
#define NoStateTrainQuery 				3
#define NoStateTrainStop 				4
#define NoStateTrainGo 					5

//#define NoStatePosEnter 				1
#define NoStatePosApproaching 			2
#define NoStatePosLeave 				3

#define NoStateSpeedMoving  			1
#define NoStateSpeedStopped				2

#define NoStateBrakesIdle				1
#define NoStateBrakesEngaged			2



//-- Failure Automata
#define NoFailureBrakesNo				0
#define NoFailureBrakesYes				1

#define NoFailureSecuredNo				0
#define NoFailureSecuredYes				1

#define NoFailureCloseNo 				0
#define NoFailureCloseYes 				1

#define NoFailureOpenNo 				0
#define NoFailureOpenYes 				1

#define NoFailureStuckNo 				0
#define NoFailureStuckYes 				1

#define NoFailureCommTrainNo 			0
#define NoFailureCommTrainYes 			1

#define NoFailureCommCrossingNo 		0
#define NoFailureCommCrossingYes 		1
//-- MAGIC NUMBERS ------------------------------------------------------------------------------



//-- STATES -------------------------------------------------------------------------------------
int StateTimerClosing = NoStateTimerClosingInactive;
int StateTimerOpen = NoStateTimerOpenInactive;
int StateCommClose = NoStateCommCloseInactive;
int StateCommQuery = NoStateCommQueryInactive;
int StateCommSecured = NoStateCommSecuredInactive;
int StateCrossing = 1;
int StateTrain = NoStateTrainIdle;
int StatePos = NoStatePosApproaching;
int StateSpeed = NoStateSpeedMoving;
int StateBrakes = NoStateBrakesIdle;

int FailureBrakes = NoFailureBrakesNo;
int FailureOdometer = 0;
int FailureSecured = NoFailureSecuredNo;
int FailureClose = NoFailureCloseNo;
int FailureOpen = NoFailureOpenNo;
int FailureStuck = NoFailureStuckNo;
int FailureCommTrain = NoFailureCommTrainNo;
int FailureCommCrossing = NoFailureCommCrossingNo;
//-- STATES -------------------------------------------------------------------------------------


//-- OTHER VARIABLES ----------------------------------------------------------------------------
int Speed = DefMaxSpeed;
int Pos = 0;
int CommQueryTimeout = 0;
int CommCloseTimeout = 0;
int CommSecuredTimeout = 0;
int TimerClosingTimeout = 0;
int TimerOpenTimeout = 0;


//-- OTHER VARIABLES ----------------------------------------------------------------------------


//-- ABBREVIATIONS ------------------------------------------------------------------------------
//-- Renames the module instances to increase readability and to better match the graphical
//-- representation of the system. In particular, when we refer to another automaton, we 
//-- actually mean its State variable in the graphical representation.

//-- Timer
#define IsStateTimerClosingInactive 	(StateTimerClosing==NoStateTimerClosingInactive)
#define IsStateTimerClosingSignal	 	(StateTimerClosing==NoStateTimerClosingSignal)
#define IsStateTimerClosingActive	 	(StateTimerClosing==NoStateTimerClosingActive)

#define IsStateTimerOpenInactive 		(StateTimerOpen==NoStateTimerOpenInactive)
#define IsStateTimerOpenSignal	 		(StateTimerOpen==NoStateTimerOpenSignal)
#define IsStateTimerOpenActive	 		(StateTimerOpen==NoStateTimerOpenActive)


//-- Communication
#define IsStateCommCloseInactive 		(StateCommClose==NoStateCommCloseInactive)
#define IsStateCommCloseSignal 			(StateCommClose==NoStateCommCloseSignal)
#define IsStateCommCloseActive 			(StateCommClose==NoStateCommCloseActive)

#define IsStateCommQueryInactive 		(StateCommQuery==NoStateCommQueryInactive)
#define IsStateCommQuerySignal 			(StateCommQuery==NoStateCommQuerySignal)
#define IsStateCommQueryActive 			(StateCommQuery==NoStateCommQueryActive)

#define IsStateCommSecuredInactive 		(StateCommSecured==NoStateCommSecuredInactive)
#define IsStateCommSecuredSignal 		(StateCommSecured==NoStateCommSecuredSignal)
#define IsStateCommSecuredActive 		(StateCommSecured==NoStateCommSecuredActive)

				
//-- Components
#define IsStateCrossingOpened 			(StateCrossing==NoStateCrossingOpened)
#define IsStateCrossingClosing 			(StateCrossing==NoStateCrossingClosing)
#define IsStateCrossingClosed 			(StateCrossing==NoStateCrossingClosed)
#define IsStateCrossingStuck			(StateCrossing==NoStateCrossingStuck)

#define IsStateTrainIdle 				(StateTrain==NoStateTrainIdle)
#define IsStateTrainWait 				(StateTrain==NoStateTrainWait)
#define IsStateTrainQuery 				(StateTrain==NoStateTrainQuery)
#define IsStateTrainStop 				(StateTrain==NoStateTrainStop)
#define IsStateTrainGo 					(StateTrain==NoStateTrainGo)

#define IsStatePosEnter 				(StatePos==NoStatePosEnter)
#define IsStatePosApproaching 			(StatePos==NoStatePosApproaching)
#define IsStatePosLeave 				(StatePos==NoStatePosLeave)

#define IsStateSpeedMoving  			(StateSpeed==NoStateSpeedMoving)
#define IsStateSpeedStopped				(StateSpeed==NoStateSpeedStopped)

#define IsStateBrakesIdle				(StateBrakes==NoStateBrakesIdle)
#define IsStateBrakesEngaged			(StateBrakes==NoStateBrakesEngaged)



//-- Failure Automata
#define IsFailureBrakesNo				(FailureBrakes==NoFailureBrakesNo)
#define IsFailureBrakesYes				(FailureBrakes==NoFailureBrakesYes)

#define IsFailureOdometerNo 			(FailureOdometer==0)
#define IsFailureOdometerNo 			(FailureOdometer>0)

#define IsFailureSecuredNo				(FailureSecured==NoFailureSecuredNo)
#define IsFailureSecuredYes				(FailureSecured==NoFailureSecuredYes)

#define IsFailureCloseNo 				(FailureClose==NoFailureCloseNo)
#define IsFailureCloseYes 				(FailureClose==NoFailureCloseYes)

#define IsFailureOpenNo 				(FailureOpen==NoFailureOpenNo)
#define IsFailureOpenYes 				(FailureOpen==NoFailureOpenYes)

#define IsFailureStuckNo 				(FailureStuck==NoFailureStuckNo)
#define IsFailureStuckYes 				(FailureStuck==NoFailureStuckYes)

#define IsFailureCommTrainNo 			(FailureCommTrain==NoFailureCommTrainNo)
#define IsFailureCommTrainYes 			(FailureCommTrain==NoFailureCommTrainYes)

#define IsFailureCommCrossingNo 		(FailureCommCrossing==NoFailureCommCrossingNo)
#define IsFailureCommCrossingYes 		(FailureCommCrossing==NoFailureCommCrossingYes)

#define IsFailureCommNo 				(IsFailureCommTrainNo && IsFailureCommCrossingNo)
#define IsFailureCommYes 				(IsFailureCommCrossingYes || IsFailureCommCrossingYes)
//-- ABBREVIATIONS ------------------------------------------------------------------------------


//-- OBSERVERS FOR VERIFICATION -----------------------------------------------------------------




//-- OBSERVERS FOR VERIFICATION -----------------------------------------------------------------


//-- MODEL --------------------------------------------------------------------------------------
active proctype ffb( ) {
  // Scheduling
  // Environment
  //   1. TrainSpeed
  //   2. TrainPosition
  // Train
  //   3. TrainControl
  //   4. Brakes
  // Communication Train -> Crossing
  //   5. CommQuery
  //   6. CommClose
  // Crossing
  //   7. CrossingControl
  //   8. TimerClosing
  //   9. TimerOpen
  // Communication Crossing -> Train
  //  10. CommSecured
  
  // Failures
  //  11. FailureBrakes
  //  12. FailureOdometer
  //  13. FailureSecured
  //  14. FailureClose
  //  15. FailureOpen
  //  16. FailureStuck
  //  17. FailureCommTrain
  //  18. FailureCommCrossing (We need a separate automata, otherwise we do not include the case, where the train sends a "Query" and the Crossing does not send a "Secured")
  
  
  do
  ::	true -> // guard
  		atomic {
		//-- ENVIRONMENT ---------------------------
		//   1. TrainSpeed
		if
			:: IsStateBrakesEngaged && (Speed >= 0) && (Speed-DefDec >= 0) -> Speed = Speed - DefDec
			:: IsStateBrakesEngaged && (Speed >= 0) && (Speed-DefDec < 0) -> Speed = 0
			:: else -> skip
		fi;
		if
			:: Speed > 0 -> StateSpeed = NoStateSpeedMoving
			:: else -> StateSpeed = NoStateSpeedStopped
		fi;
		
		//   2. TrainPosition
		if
			:: Pos + Speed >= DefEndPos -> Pos = DefEndPos
			:: else -> Pos = Pos + Speed
		fi;
		if
			:: IsStatePosApproaching && Pos >= DefEndPos -> StatePos = NoStatePosLeave
			:: else -> skip
		fi;
		//-- ENVIRONMENT ---------------------------
		
		
		//-- TRAIN ---------------------------------		
		//   3. TrainControl
		if
			:: IsStateTrainIdle && Pos >= DefClosePos -> StateTrain = NoStateTrainWait
			:: IsStateTrainWait && Pos >= DefQueryPos -> StateTrain = NoStateTrainQuery
			:: IsStateTrainQuery && IsStateCommSecuredActive -> StateTrain = NoStateTrainGo
			:: IsStateTrainQuery && Pos >= DefStopPos -> StateTrain = NoStateTrainStop
			:: else -> skip
		fi;		
		
		//   4. Brakes
		if
			:: IsStateTrainStop && IsFailureBrakesNo -> StateBrakes = NoStateBrakesEngaged
			:: IsStateBrakesEngaged & ! IsFailureBrakesNo -> StateBrakes = NoStateBrakesIdle
			:: else -> skip
		fi;		
		//-- TRAIN ---------------------------------
		
		
		//-- COMMUNICATION TRAIN -> CROSSING -------
		//   5. CommQuery
		// Condition is Train = Wait & Pos >= QueryPos & FailureComm = No
		if
			:: IsStateCommQueryInactive && IsStateTrainQuery && IsFailureCommTrainNo ->
			   CommQueryTimeout = DefCommDelay;
			   StateCommQuery = NoStateCommQueryActive
			:: IsStateCommQueryActive && (CommQueryTimeout > 0) ->
			   CommQueryTimeout = CommQueryTimeout - 1
			:: IsStateCommQueryActive && (CommQueryTimeout == 0) ->
			   StateCommQuery = NoStateCommQuerySignal
			:: IsStateCommQuerySignal ->
			   StateCommQuery = NoStateCommQueryInactive
			:: else -> skip
		fi;
		
		//   6. CommClose
		// Condition is Train = Idle & Pos >= ClosePos & FailureComm = No
		if
			:: IsStateCommCloseInactive && IsStateTrainWait && IsFailureCommTrainNo ->
			   CommCloseTimeout = DefCommDelay;
			   StateCommClose = NoStateCommCloseActive
			:: IsStateCommCloseActive && (CommCloseTimeout > 0) ->
			   CommCloseTimeout = CommCloseTimeout - 1
			:: IsStateCommCloseActive && (CommCloseTimeout == 0) ->
			   StateCommClose = NoStateCommCloseSignal
			:: IsStateCommCloseSignal ->
			   StateCommClose = NoStateCommCloseInactive
			:: else -> skip
		fi;
		//-- COMMUNICATION TRAIN -> CROSSING -------
					
		
		//-- CROSSING ------------------------------
		//   7. CrossingControl
		if
			:: IsStateCrossingOpened && IsStateCommCloseSignal && IsFailureCloseNo -> StateCrossing = NoStateCrossingClosing
			:: IsStateCrossingClosing && IsStateTimerClosingSignal && IsFailureStuckNo -> StateCrossing = NoStateCrossingClosed
			:: IsStateCrossingStuck && ! IsFailureStuckNo -> StateCrossing = NoStateCrossingClosed
			:: IsStateCrossingStuck && ! IsFailureStuckNo -> StateCrossing = NoStateCrossingClosing
			:: IsStateCrossingStuck && ! IsFailureStuckNo -> StateCrossing = NoStateCrossingOpened
			:: IsStateCrossingClosed && (IsStateTimerOpenSignal || Pos >= DefSensorPos || ! IsFailureOpenNo) -> StateCrossing = NoStateCrossingOpened
			:: IsStateCrossingClosed && ! IsFailureStuckNo && (IsStateTimerClosingSignal || Pos >= DefSensorPos) -> StateCrossing = NoStateCrossingStuck
			:: else -> skip
		fi;  
  
		//   8. TimerClosing
		// Condition is Crossing = Opened & CommClose = Signal
		if
			:: IsStateTimerClosingInactive && IsStateCrossingClosing ->
			   TimerClosingTimeout = DefClosingDelay;
			   StateTimerClosing = NoStateTimerClosingActive
			:: IsStateTimerClosingActive && (TimerClosingTimeout > 0) ->
			   TimerClosingTimeout = TimerClosingTimeout - 1
			:: IsStateTimerClosingActive && (TimerClosingTimeout == 0) ->
			   StateTimerClosing = NoStateTimerClosingSignal
			:: IsStateTimerClosingSignal ->
			   StateTimerClosing = NoStateTimerClosingInactive
			:: else -> skip
		fi;
		
		//  9. TimerOpen
		// Condition is Crossing = Closed
		if
			:: IsStateTimerOpenInactive && IsStateCrossingClosed ->
			   TimerOpenTimeout = DefCloseTimeout;
			   StateTimerOpen = NoStateTimerOpenActive
			:: IsStateTimerOpenActive && (TimerOpenTimeout > 0) ->
			   TimerOpenTimeout = TimerOpenTimeout - 1
			:: IsStateTimerOpenActive && (TimerOpenTimeout == 0) ->
			   StateTimerOpen = NoStateTimerOpenSignal
			:: IsStateTimerOpenSignal ->
			   StateTimerOpen = NoStateTimerOpenInactive
			:: else -> skip
		fi;
		//-- CROSSING ------------------------------
								
		//-- COMMUNICATION CROSSING -> TRAIN -------
		//   10. CommSecured
		// Condition is (Crossing = Closed & CommQuery = Signal & FailureComm = No) | (Crossing != Closed & CommQuery = Signal & FailureComm = No & FailureSecured != No)
		if
			:: IsStateCommSecuredInactive && ((IsStateCrossingClosed && IsStateCommQuerySignal && IsFailureCommCrossingNo) || ( (! IsStateCrossingClosed) && IsStateCommQuerySignal && IsFailureCommCrossingNo && ( !IsFailureSecuredNo))) ->
			   CommSecuredTimeout = DefCommDelay;
			   StateCommSecured = NoStateCommSecuredActive
			:: IsStateCommSecuredActive && (CommSecuredTimeout > 0) ->
			   CommSecuredTimeout = CommSecuredTimeout - 1
			:: IsStateCommSecuredActive && (CommSecuredTimeout == 0) ->
			   StateCommSecured = NoStateCommSecuredSignal
			:: IsStateCommSecuredSignal ->
			   skip
			   //StateCommSecured = NoStateCommSecuredInactive
			:: else -> skip
		fi;
		//-- COMMUNICATION CROSSING -> TRAIN -------
				
				
		//-- FAILURES ------------------------------
		//  11. FailureBrakes (persistent)
		if
			:: true -> FailureBrakes = NoFailureBrakesYes
			:: FailureBrakes == NoFailureBrakesNo -> FailureBrakes = NoFailureBrakesNo
		fi;
		
		//  12. FailureOdometer (deviates)
		if
			:: true -> FailureOdometer = 0
			:: true -> FailureOdometer = -1
			:: true -> FailureOdometer = -2
			:: true -> FailureOdometer = -3
		fi;
		//  13. FailureSecured (transient)
		if
			:: true -> FailureSecured = NoFailureSecuredYes
			:: true -> FailureSecured = NoFailureSecuredNo
		fi;
		//  14. FailureClose (transient))
		if
			:: true -> FailureClose = NoFailureCloseYes
			:: true -> FailureClose = NoFailureCloseNo
		fi;
		//  15. FailureOpen (transient)
		if
			:: true -> FailureOpen = NoFailureOpenYes
			:: true -> FailureOpen = NoFailureOpenNo
		fi;
		//  16. FailureStuck (persistent)
		if
			:: true -> FailureStuck = NoFailureStuckYes
			:: IsFailureStuckNo -> FailureStuck = NoFailureStuckNo
		fi;
		//  17. FailureCommTrain (transient)
		if
			:: true -> FailureCommTrain = NoFailureCommTrainYes
			:: true -> FailureCommTrain = NoFailureCommTrainNo
		fi;		
		//  18. FailureCommCrossing (transient)
		if
			:: true -> FailureCommCrossing = NoFailureCommCrossingYes
			:: true -> FailureCommCrossing = NoFailureCommCrossingNo
		fi;		
		//-- FAILURES ------------------------------
  
  		} //atomic
  od  
}
//-- MODEL --------------------------------------------------------------------------------------



//-- VERIFICATION -------------------------------------------------------------------------------
#define DefHazard (Pos <= DefCrossingPos && (DefCrossingPos < Pos + Speed) && ! IsStateCrossingClosed)


		
// Functional Correctness DCCA
//ltl FunctionalCorrectness { 
//	! ((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureSecuredNo && IsFailureCloseNo && IsFailureOpenNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}
	
// Single Points of Failure -----------------------------------------------------------------------
//ltl Single_FailureBrakes { 
//	! ((FailureOdometer == 0 && IsFailureSecuredNo && IsFailureCloseNo && IsFailureOpenNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}
	
//ltl Single_FailureOdometer { 
//	!((IsFailureBrakesNo && IsFailureSecuredNo && IsFailureCloseNo && IsFailureOpenNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}

//ltl Single_FailureSecured { 
//	!((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureCloseNo && IsFailureOpenNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}

//ltl Single_FailureClose { 
//	!((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureSecuredNo && IsFailureOpenNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}
	
//fails
//ltl Single_FailureOpen { 
//	!((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureSecuredNo && IsFailureCloseNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}
	
//ltl Single_FailureStuck { 
//	!((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureSecuredNo && IsFailureCloseNo && IsFailureOpenNo && IsFailureCommNo) U (DefHazard))
//}
	
//ltl Single_FailureComm { 
//	!((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureSecuredNo && IsFailureCloseNo && IsFailureOpenNo && IsFailureStuckNo) U (DefHazard))
//}
	
// Combinations of 2 Failures ---------------------------------------------------------------------
//fails
//ltl FailureComm_FailureOdometer { 
//	!((IsFailureBrakesNo && IsFailureSecuredNo && IsFailureCloseNo && IsFailureOpenNo && IsFailureStuckNo) U (DefHazard))
//}

//fails	
//ltl FailureClose_FailureBrakes { 
//	!((FailureOdometer == 0 && IsFailureSecuredNo && IsFailureOpenNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}

//fails
//ltl FailureComm_FailureBrakes { 
//	!((FailureOdometer == 0 && IsFailureSecuredNo && IsFailureCloseNo && IsFailureOpenNo && IsFailureStuckNo) U (DefHazard))
//}

//fails	
//ltl FailureStuck_FailureBrakes { 
//	!((FailureOdometer == 0 && IsFailureSecuredNo && IsFailureCloseNo && IsFailureOpenNo && IsFailureCommNo) U (DefHazard))
//}

//fails	
//ltl FailureClose_FailureOdometer { 
//	!((IsFailureBrakesNo && IsFailureSecuredNo && IsFailureOpenNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}

//fails	
//ltl FailureStuck_FailureOdometer { 
//	!((IsFailureBrakesNo && IsFailureSecuredNo && IsFailureCloseNo && IsFailureOpenNo && IsFailureCommNo) U (DefHazard))
//}

//fails	
//ltl FailureClose_FailureSecured { 
//	!((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureOpenNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}

//fails
//ltl FailureComm_FailureSecured { 
//	!((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureCloseNo && IsFailureOpenNo && IsFailureStuckNo) U (DefHazard))
//}
	
//fails
//ltl FailureStuck_FailureSecured { 
//	!((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureCloseNo && IsFailureOpenNo && IsFailureCommNo) U (DefHazard))
//}

//Needs Depth 20000. Takes a long time (31.2 seconds)
//ltl FailureBrakes_FailureOdometer { 
//	!((IsFailureSecuredNo && IsFailureCloseNo && IsFailureOpenNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}
	
//ltl FailureBrakes_FailureSecured { 
//	!((FailureOdometer == 0 && IsFailureCloseNo && IsFailureOpenNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}
	
//ltl FailureSecured_FailureOdometer { 
//	!((IsFailureBrakesNo && IsFailureCloseNo && IsFailureOpenNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}
	
//ltl FailureClose_FailureStuck { 
//	!((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureSecuredNo && IsFailureOpenNo && IsFailureCommNo) U (DefHazard))
//}
	
//ltl FailureClose_FailureComm { 
//	!((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureSecuredNo && IsFailureOpenNo && IsFailureStuckNo) U (DefHazard))
//}

// Needs Depth 30000. Still fast (9 seconds)	
//ltl FailureStuck_FailureComm { 
//	!((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureSecuredNo && IsFailureCloseNo && IsFailureOpenNo) U (DefHazard))
//}
	
// Combinations of 3 Failures ---------------------------------------------------------------------
// Needs Depth 50000. Still fast (15 seconds)	
//ltl FailureClose_FailureStuck_FailureComm { 
//	!((IsFailureBrakesNo && FailureOdometer == 0 && IsFailureOpenNo && IsFailureSecuredNo) U (DefHazard))
//}

// Needs Depth 20000. Quite slow (57.9 seconds)
//ltl FailureBrakes_FailureSecured_FailureOdometer { 
//	!((IsFailureCloseNo && IsFailureOpenNo && IsFailureStuckNo && IsFailureCommNo) U (DefHazard))
//}



ltl hazardNeverOccurs { [] ! (DefHazard) }


//-- VERIFICATION -------------------------------------------------------------------------------
