//-- SCALES -------------------------------------------------------------------------------------
#define DefPosScale 	3	// 1 unit represents PosScale meters
#define DefTimeScale 	2	// 1 unit represents TimeScale seconds
//-- SCALES -------------------------------------------------------------------------------------


//-- MISC PARAMETERS ----------------------------------------------------------------------------
#define DefSafetyMargin 	(350 / DefPosScale) 							//-- 92m safety margin for odometer failure -1 and 258m technical margin -> 45m rounding errors + 174m 2 time steps delay + 39m discrete position modeling
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

#define NoFailureCommNo 				0
#define NoFailureCommYes 				1
//-- MAGIC NUMBERS ------------------------------------------------------------------------------



//-- STATES -------------------------------------------------------------------------------------
int StateTimerClosing = 1;
int StateTimerOpen = 1;
int StateCommClose = NoStateCommCloseInactive;
int StateCommQuery = NoStateCommQueryInactive;
int StateCommSecured = NoStateCommSecuredInactive;
int StateCrossing = 1;
int StateTrain = 1;
int StatePos = NoStatePosApproaching;
int StateSpeed = NoStateSpeedMoving;
int StateBrakes = 1;

int FailureBrakes = NoFailureBrakesNo;
int FailureOdometer = 0;
int FailureSecured = NoFailureSecuredNo;
int FailureClose = NoFailureCloseNo;
int FailureOpen = NoFailureOpenNo;
int FailureStuck = NoFailureStuckNo;
int FailureComm = NoFailureCommNo;
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

#define IsFailureCommNo 				(FailureComm==NoFailureCommNo)
#define IsFailureCommYes 				(FailureComm==NoFailureCommYes)
//-- ABBREVIATIONS ------------------------------------------------------------------------------


active proctype ffb( ) {
  // Scheduling
  // Environment
  //   1. TrainSpeed
  //   2. TrainPosition
  // Communication
  //   3. CommQuery
  //   4. CommClose
  //   5. CommSecured
  // Train
  //   6. TrainControl
  //   7. Brakes
  // Crossing
  //   8. CrossingControl
  //   9. TimerClosing
  //  10. TimerOpen
  // Failures
  //  11. FailureBrakes
  //  12. FailureOdometer
  //  13. FailureSecured
  //  14. FailureClose
  //  15. FailureOpen
  //  16. FailureStuck
  //  17. FailureComm
  
  
  do
  ::	true -> // guard
  
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
			:: StatePos = NoStatePosApproaching && Pos >= DefEndPos -> StatePos = NoStatePosLeave
			:: else -> skip
		fi;
		
		//-- COMMUNICATION -------------------------
		//   3. CommQuery
		// Condition is Train = Wait & Pos >= QueryPos & FailureComm = No
		if
			:: StateCommQuery == NoStateCommQueryInactive && (IsStateTrainWait && Pos >= DefQueryPos && IsFailureCommNo) ->
			   CommQueryTimeout = 30;
			   StateCommQuery = NoStateCommQueryActive
			:: StateCommQuery == NoStateCommQueryActive && (CommQueryTimeout > 0) ->
			   CommQueryTimeout = CommQueryTimeout - 1
			:: StateCommQuery == NoStateCommQueryActive && (CommQueryTimeout == 0) ->
			   StateCommQuery = NoStateCommQuerySignal
			:: StateCommQuery == NoStateCommQuerySignal ->
			   StateCommQuery = NoStateCommQueryInactive
			:: else -> skip
		fi;
		
		//   4. CommClose
		// Condition is Train = Idle & Pos >= ClosePos & FailureComm = No
		if
			:: StateCommClose == NoStateCommCloseInactive && (IsStateTrainIdle && Pos >= DefClosePos && IsFailureCommNo) ->
			   CommCloseTimeout = 30;
			   StateCommClose = NoStateCommCloseActive
			:: StateCommClose == NoStateCommCloseActive && (CommCloseTimeout > 0) ->
			   CommCloseTimeout = CommCloseTimeout - 1
			:: StateCommClose == NoStateCommCloseActive && (CommCloseTimeout == 0) ->
			   StateCommClose = NoStateCommCloseSignal
			:: StateCommClose == NoStateCommCloseSignal ->
			   StateCommClose = NoStateCommCloseInactive
			:: else -> skip
		fi;
		
		//   5. CommSecured
		// Condition is (Crossing = Closed & CommQuery = Signal & FailureComm = No) | (Crossing != Closed & CommQuery = Signal & FailureComm = No & FailureSecured != No)
		if
			:: StateCommSecured == NoStateCommSecuredInactive && ((IsStateCrossingClosed && IsStateCommQuerySignal && IsFailureCommNo) || ( (! IsStateCrossingClosed) && IsStateCommQuerySignal && IsFailureCommNo && ( !IsFailureSecuredNo))) ->
			   CommSecuredTimeout = 30;
			   StateCommSecured = NoStateCommSecuredActive
			:: StateCommSecured == NoStateCommSecuredActive && (CommSecuredTimeout > 0) ->
			   CommSecuredTimeout = CommSecuredTimeout - 1
			:: StateCommSecured == NoStateCommSecuredActive && (CommSecuredTimeout == 0) ->
			   StateCommSecured = NoStateCommSecuredSignal
			:: StateCommSecured == NoStateCommSecuredSignal ->
			   StateCommSecured = NoStateCommSecuredInactive
			:: else -> skip
		fi;
  
  
		//   9. TimerClosing
		// Condition is Crossing = Opened & CommClose = Signal
		if
			:: StateTimerClosing == NoStateTimerClosingInactive && (IsStateCrossingOpened && IsStateCommCloseSignal) ->
			   TimerClosingTimeout = 30;
			   StateTimerClosing = NoStateTimerClosingActive
			:: StateTimerClosing == NoStateTimerClosingActive && (TimerClosingTimeout > 0) ->
			   TimerClosingTimeout = TimerClosingTimeout - 1
			:: StateTimerClosing == NoStateTimerClosingActive && (TimerClosingTimeout == 0) ->
			   StateTimerClosing = NoStateTimerClosingSignal
			:: StateTimerClosing == NoStateTimerClosingSignal ->
			   StateTimerClosing = NoStateTimerClosingInactive
			:: else -> skip
		fi;
		//  10. TimerOpen
		// Condition is Crossing = Closed
		if
			:: StateTimerOpen == NoStateTimerOpenInactive && (IsStateCrossingClosed) ->
			   TimerOpenTimeout = 30;
			   StateTimerOpen = NoStateTimerOpenActive
			:: StateTimerOpen == NoStateTimerOpenActive && (TimerOpenTimeout > 0) ->
			   TimerOpenTimeout = TimerOpenTimeout - 1
			:: StateTimerOpen == NoStateTimerOpenActive && (TimerOpenTimeout == 0) ->
			   StateTimerOpen = NoStateTimerOpenSignal
			:: StateTimerOpen == NoStateTimerOpenSignal ->
			   StateTimerOpen = NoStateTimerOpenInactive
			:: else -> skip
		fi;
				
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
			:: FailureStuck == NoFailureStuckNo -> FailureStuck = NoFailureStuckNo
		fi;
		//  17. FailureComm (transient)
		if
			:: true -> FailureComm = NoFailureCommYes
			:: true -> FailureComm = NoFailureCommNo
		fi		
  od  
}