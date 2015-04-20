component backupRecoverySystem {
	component in {
		sourceValueField : int<0..100> = 1;
		
		determineSourceValueR ( );
		
		determineSourceValueP ( ) {
			choice {
				true => { sourceValueField := 1; }
				true => { sourceValueField := 2; }
				true => { sourceValueField := 3; }
				true => { sourceValueField := 4; }
				true => { sourceValueField := 5; }
			}
		}
		
		getSourceValueP ( inout sourceValueInout : int ) {
			sourceValueInout := sourceValueField;
		}
		
		in.determineSourceValueR = instantly in.determineSourceValueP
		
		step {
			determineSourceValueR ( );
		}
	}

	component s1 {		
		senseSourceValueR ( inout sourceValueInout : int );
	
		getSensorValueP ( inout sensorValueInout : int ) {
			senseSourceValueR ( inout sensorValueInout );
		}
		
		step { }
	}
	
	component s2 {		
		senseSourceValueR ( inout sourceValueInout : int );
	
		getSensorValueP ( inout sensorValueInout : int ) {
			senseSourceValueR ( inout sensorValueInout );
		}
		
		step { }
	}
	
	component a1 {
		isActiveField : bool = true;
		
		getSensorValue1R ( inout sensorValueInout : int );
		getSensorValue2R ( inout sensorValueInout : int );
		
	
		getArithmeticalValueP ( inout arithmeticalValueInout : int ) {
			int sensorValue1Local;
			int sensorValue2Local;
			getSensorValue1R ( inout sensorValue1Local ) ;
			getSensorValue2R ( inout sensorValue2Local ) ;
			arithmeticalValueInout := sensorValue1Local;
		}
		
		doSensorValuesMatchP ( inout sensorValuesMatchInout : bool ) {
			int sensorValue1Local ;
			int sensorValue2Local ;
			getSensorValue1R ( inout sensorValue1Local ) ;
			getSensorValue2R ( inout sensorValue2Local ) ;
			sensorValuesMatchInout := sensorValue1Local == sensorValue2Local;
		}
		
		deactivateP ( ) {
			choice {
				(isActiveField ) => { isActiveField := false; }
				!(isActiveField ) => { }
			}
		}
						
		step { }
	}
	
	component a2 {
		isActiveField : bool = false;
		
		getSensorValueR ( inout sensorValueInout : int );
	
		getArithmeticalValueP ( inout arithmeticalValueInout : int ) {
			getSensorValueR ( inout arithmeticalValueInout ) ;
		}
		
		activateP ( ) {
			choice {
				(isActiveField) => {  }
				!(isActiveField) => { isActiveField := true; }
			}
		}
		
		step { }
	}
	
	component monitor {
		monitorIsActive : bool = true;	
	
		doSensorValuesMatchR ( inout sensorValuesMatchInout : bool );
		switchArithmeticalUnitR_PartActivate ( );
		switchArithmeticalUnitR_PartDeactivate ( );
		switchArithmeticalUnitR_PartSwitchOutput ( );
	
		
		step {
			bool doSensorValuesMatchLocal;
			choice {
				monitorIsActive => {
					doSensorValuesMatchR ( inout doSensorValuesMatchLocal) ;
					choice {
						doSensorValuesMatchLocal => {}
						! doSensorValuesMatchLocal => {
							switchArithmeticalUnitR_PartActivate () ;
							switchArithmeticalUnitR_PartDeactivate () ;
							switchArithmeticalUnitR_PartSwitchOutput ();
							monitorIsActive := false;
						}
					}
				}
				! monitorIsActive => {}
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
				useA1 => { getArithmeticalValue1R ( inout arithmeticalValueLocal ); }
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
		step monitor;
		step out;
	}
}
