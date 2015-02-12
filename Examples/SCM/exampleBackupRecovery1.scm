component backupRecoverySystem {
	component in {
		sourceValueField : int = 1;
		
		determineSourceValueR ( );
		
		determineSourceValueP ( ) {
			locals{
			}
			choice {
				true => { sourceValueField := 1; }
				true => { sourceValueField := 2; }
				true => { sourceValueField := 3; }
				true => { sourceValueField := 4; }
				true => { sourceValueField := 5; }
			}
		}
		
		getSourceValueP ( inout sourceValueInout : int ) {
			locals{
			}
			sourceValueInout := sourceValueField;
		}
		
		determineSourceValueR = instantly determineSourceValueP
		
		step {
			locals{
			}
			determineSourceValueR ( );
		}
	}

	component s1 {		
		senseSourceValueR ( inout sourceValueInout : int );
	
		getSensorValueP ( inout sensorValueInout : int ) {
			locals{
			}
			senseSourceValueR ( inout sensorValueInout );
		}
		
		step { locals{	} }
	}
	
	component s2 {		
		senseSourceValueR ( inout sourceValueInout : int );
	
		getSensorValueP ( inout sensorValueInout : int ) {
			locals{
			}
			senseSourceValueR ( inout sensorValueInout );
		}
		
		step { locals{} }
	}
	
	component a1 {
		isActiveField : bool = true;
		
		getSensorValue1R ( inout sensorValueInout : int );
		getSensorValue2R ( inout sensorValueInout : int );
		
	
		getArithmeticalValueP ( inout arithmeticalValueInout : int ) {
			locals{
				int sensorValue1Local;
				int sensorValue2Local;
			}
			getSensorValue1R ( inout sensorValue1Local ) ;
			getSensorValue2R ( inout sensorValue2Local ) ;
			arithmeticalValueInout := sensorValue1Local;
		}
		
		doSensorValuesMatchP ( inout sensorValuesMatchInout : bool ) {
			locals{
				int sensorValue1Local ;
				int sensorValue2Local ;
			}
			getSensorValue1R ( inout sensorValue1Local ) ;
			getSensorValue2R ( inout sensorValue2Local ) ;
			sensorValuesMatchInout := sensorValue1Local == sensorValue2Local;
		}
		
		deactivateP ( ) {
			locals{
			}
			choice {
				(isActiveField ) => { isActiveField := false; }
				!(isActiveField ) => { }
			}
		}
						
		step { locals{} }
	}
	
	component a2 {
		isActiveField : bool = false;
		
		getSensorValueR ( inout sensorValueInout : int );
	
		getArithmeticalValueP ( inout arithmeticalValueInout : int ) {
			locals{}
			getSensorValueR ( inout arithmeticalValueInout ) ;
		}
		
		activateP ( ) {
			locals{}
			choice {
				(isActiveField) => {  }
				!(isActiveField) => { isActiveField := false; }
			}
		}
		
		step {	locals{}  }
	}
	
	component monitor {
		doSensorValuesMatchR ( inout sensorValuesMatchInout : bool );
		switchArithmeticalUnitR_PartActivate ( );
		switchArithmeticalUnitR_PartDeactivate ( );
		switchArithmeticalUnitR_PartSwitchOutput ( );
	
		
		step {			
			locals{
				bool doSensorValuesMatchLocal;
			}
			doSensorValuesMatchR ( inout doSensorValuesMatchLocal) ;
			choice {
				doSensorValuesMatchLocal => {}
				! doSensorValuesMatchLocal => {
					switchArithmeticalUnitR_PartActivate () ;
					switchArithmeticalUnitR_PartDeactivate () ;
					switchArithmeticalUnitR_PartSwitchOutput ();
				}
			}
		}
	}

	component out {
		useA1 : bool = true;
		result : int = 1;
		
		getArithmeticalValue1R ( inout arithmeticalValueInout : int );
		getArithmeticalValue2R ( inout arithmeticalValueInout : int );
		
		switchArithmeticalUnitP ( ) {
			locals{
			}
			useA1 := ! useA1;
		}
		
		step {			
			locals{
				int arithmeticalValueLocal;
			}
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
	backupRecoverySystem.monitor.doSensorValuesMatchR = instantly backupRecoverySystem.a1.doSensorValuesMatchP	
	backupRecoverySystem.monitor.switchArithmeticalUnitR_PartActivate = instantly backupRecoverySystem.a2.activateP
	backupRecoverySystem.monitor.switchArithmeticalUnitR_PartDeactivate = instantly backupRecoverySystem.a1.deactivateP
	backupRecoverySystem.monitor.switchArithmeticalUnitR_PartSwitchOutput = instantly backupRecoverySystem.out.switchArithmeticalUnitP
	backupRecoverySystem.out.getArithmeticalValue1R = instantly backupRecoverySystem.a1.getArithmeticalValueP
	backupRecoverySystem.out.getArithmeticalValue2R = instantly backupRecoverySystem.a2.getArithmeticalValueP
	
	step {
		locals{}
		step in;
		step monitor;
		step out;
	}
}
