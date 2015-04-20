component backupRecoverySystem {
	component in {
		sourceValueField : int<0..100> = 1;
		
		getSourceValueP ( inout sourceValueInout : int ) {
			sourceValueInout := sourceValueField;
		}
		
		step {
			choice {
				true => { sourceValueField := 1; }
				true => { sourceValueField := 2; }
				true => { sourceValueField := 3; }
				true => { sourceValueField := 4; }
				true => { sourceValueField := 5; }
			}
		}
	}

	component s1 {
		sensorValueField : int<0..100> = 1;

		senseSourceValueR ( inout sourceValueInout : int );
	
		getSensorValueP ( inout sensorValueInout : int ) {
			sensorValueInout := sensorValueField;
		}
		
		step {
			int sensorValueInout;
			senseSourceValueR ( inout sensorValueInout ) ;
			sensorValueField := sensorValueInout;
		}
	}
	
	component s2 {
		sensorValueField : int<0..100> = 1;

		senseSourceValueR ( inout sourceValueInout : int );
	
		getSensorValueP ( inout sensorValueInout : int ) {
			sensorValueInout := sensorValueField;
		}
		
		step {
			int sensorValueInout;
			senseSourceValueR ( inout sensorValueInout ) ;
			sensorValueField := sensorValueInout;
		}
	}
	
	component a1 {
		isActiveField : bool = true;
		arithmeticalValueField : int<0..100> = 1;
		doSensorValuesMatchField : bool = true;
	
		getSensorValue1R ( inout sensorValueInout : int );
		getSensorValue2R ( inout sensorValueInout : int );
		
	
		getArithmeticalValueP ( inout arithmeticalValueInout : int ) {
			arithmeticalValueInout := arithmeticalValueField;
		}
		
		doSensorValuesMatchP ( inout sensorValuesMatchInout : bool ) {
			sensorValuesMatchInout := doSensorValuesMatchField;
		}
		
		deactivateP ( ) {
			choice {
				(isActiveField) => { isActiveField := false; }
				!(isActiveField) => { }
			}
		}
						
		step {
			int sensorValue1Local;
			int sensorValue2Local;
			choice {
				(isActiveField) => {
					getSensorValue1R ( inout sensorValue1Local ) ;
					getSensorValue2R ( inout sensorValue2Local ) ;
					arithmeticalValueField := sensorValue1Local ;
					doSensorValuesMatchField := sensorValue1Local == sensorValue2Local;
			 	}
				!(isActiveField) => {}
			}
			
		}
	}
	
	component a2 {
		isActiveField : bool = false;
		arithmeticalValueField : int<0..100> = 1;
		
		getSensorValueR ( inout sensorValueInout : int );
	
		getArithmeticalValueP ( inout arithmeticalValueInout : int ) {
			arithmeticalValueInout := arithmeticalValueField;
		}
		
		activateP ( ) {
			choice {
				(isActiveField) => { }
				!(isActiveField) => { isActiveField := true; }
			}
		}
		
		step {
			int arithmeticalValueInout;
			choice {
				(isActiveField) => {
					getSensorValueR ( inout arithmeticalValueInout ) ;
					arithmeticalValueField := arithmeticalValueInout;
				}
				(isActiveField) => {}
			}
		}
	}
	
	component monitor {
		doSensorValuesMatchR ( inout sensorValuesMatchInout : bool );
		switchArithmeticalUnitR_PartActivate ( );
		switchArithmeticalUnitR_PartDeactivate ( );
		switchArithmeticalUnitR_PartSwitchOutput ( );
	
		
		step {
			bool doSensorValuesMatchLocal;
			doSensorValuesMatchR ( inout doSensorValuesMatchLocal) ;
			choice {
				doSensorValuesMatchLocal => { } 
				! doSensorValuesMatchLocal => {
					switchArithmeticalUnitR_PartActivate ( ) ;
					switchArithmeticalUnitR_PartDeactivate ( ) ;
					switchArithmeticalUnitR_PartSwitchOutput ( ) ;
				}
			}			
		}
	}

	component out {
		useA1 : bool = true;
		result : int<0..100> = 1;
		
		getArithmeticalValue1R ( inout arithmeticalValueInout : int );
		getArithmeticalValue2R ( inout arithmeticalValueInout : int );
		
		switchArithmeticalUnitP ( ) {
			useA1 := ! useA1;
		}
		
		step {
			int arithmeticalValueLocal;
			choice {
				useA1 => {getArithmeticalValue1R ( inout arithmeticalValueLocal ); }
				! useA1 =>  {getArithmeticalValue2R ( inout arithmeticalValueLocal ); }
			}			
			result := arithmeticalValueLocal;
		}
	}
	
		
	backupRecoverySystem.s1.senseSourceValueR = instantly backupRecoverySystem.in.getSourceValueP
	backupRecoverySystem.s2.senseSourceValueR = instantly backupRecoverySystem.in.getSourceValueP
	backupRecoverySystem.a1.getSensorValue1R = instantly backupRecoverySystem.s1.getSensorValueP
	backupRecoverySystem.a1.getSensorValue2R = instantly backupRecoverySystem.s2.getSensorValueP
	backupRecoverySystem.a2.getSensorValueR = instantly backupRecoverySystem.s2.getSensorValueP
	backupRecoverySystem.monitor.doSensorValuesMatchR = instantly backupRecoverySystem.a1.doSensorValuesMatchP	
	backupRecoverySystem.monitor.switchArithmeticalUnitR_PartActivate = instantly backupRecoverySystem.a2.activateP
	backupRecoverySystem.monitor.switchArithmeticalUnitR_PartDeactivate = instantly backupRecoverySystem.a1.deactivateP
	backupRecoverySystem.monitor.switchArithmeticalUnitR_PartSwitchOutput = instantly backupRecoverySystem.out.switchArithmeticalUnitP
	backupRecoverySystem.out.getArithmeticalValue1R = instantly backupRecoverySystem.a1.getArithmeticalValueP
	backupRecoverySystem.out.getArithmeticalValue2R = instantly backupRecoverySystem.a2.getArithmeticalValueP
	
	step {
		step in;
		step s1;
		step s2;
		step a1;
		step monitor;
		step a2;
		step out;
	}
}
