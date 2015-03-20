//-- SCALES -------------------------------------------------------------------------------------
#define PosScale 	3	// 1 unit represents PosScale meters
#define TimeScale 	2	// 1 unit represents TimeScale seconds
//-- SCALES -------------------------------------------------------------------------------------

//-- POSITIONS ----------------------------------------------------------------------------------
//-- The train's position ranges from 0 to EndPos. We are not interested in the train's actual
//-- position if it falls outside that range.		
#define EndPos 		(10000 / PosScale)	//-- 10km
#define SensorPos 	(9300 / PosScale)	//-- 9,3km
#define CrossingPos (9000 / PosScale)	//-- 9km

#define VirtualSpeed 	(Speed + failureOdometer.Delta > 0 ? Speed + failureOdometer.Delta : 0)
#define ClosePos 		(QueryPos - (CommDelay + ClosingDelay) * VirtualSpeed - SafetyMargin)
#define QueryPos 		(StopPos - 2 * CommDelay * VirtualSpeed - SafetyMargin)
#define StopPos 		(CrossingPos - VirtualSpeed * VirtualSpeed / (2 * Dec) - SafetyMargin)
//-- POSITIONS ----------------------------------------------------------------------------------

//-- MISC PARAMETERS ----------------------------------------------------------------------------
#define SafetyMargin 	(350 / PosScale) 							//-- 92m safety margin for odometer failure -1 and 258m technical margin -> 45m rounding errors + 174m 2 time steps delay + 39m discrete position modeling
#define CommDelay 		(2 / TimeScale)							//-- 2s
#define ClosingDelay 	(60 / TimeScale)							//-- 60s
#define CloseTimeout 	(240 / TimeScale)							//-- 240s
#define MaxSpeed 		(44 * TimeScale / PosScale)				//-- 160km/h = 44m/s
#define Dec 			(1 * TimeScale * TimeScale / PosScale)	//-- 1m/s^2 -> at 160km/h, the train stops after 0,97km
//-- MISC PARAMETERS ----------------------------------------------------------------------------


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

#define NoStatePosEnter 				1
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
int StateCommClose = 1;
int StateCommQuery = 1;
int StateCommSecured = 1;
int StateCrossing = 1;
int StateTrain = 1;
int StatePos = 1;
int StateSpeed = 1;
int StateBrakes = 1;

int FailureBrakes = 0;
int FailureOdometer = 0;
int FailureSecured = 0;
int FailureClose = 0;
int FailureOpen = 0;
int FailureStuck = 0;
int FailureComm = 0;
//-- STATES -------------------------------------------------------------------------------------



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
		fi;
		
  od
  
}