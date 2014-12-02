component backupRecoverySystem {
	component in {
		sourceValueField : int = 1;
		
		determineSourceValueR ( )
		
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
			determineSourceValueR ( )
		}
	}

	component s1 {		
		senseSourceValueR ( inout sourceValueInout : int )
	
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
		
		getSensorValue1R ( inout sensorValueInout : int )
		getSensorValue2R ( inout sensorValueInout : int )
		
	
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
		isActiveField = false
		
		getSensorValueR ( ; sensorValueInout : int )
	
		getArithmeticalValueP ( ; arithmeticalValueInout : int ) {
			locals{}
			getSensorValueR ( ; arithmeticalValueInout ) 
		}
		
		activateP ( ; ) {
			locals{}
			     (isActiveField) => { skip }
			||| !(isActiveField) => { isActiveField := false }
		}
		
		step {	locals{} skip }
	}
	
	component monitor {
		doSensorValuesMatchR ( inout sensorValuesMatchInout : bool )
		switchArithmeticalUnitR_PartActivate ( )
		switchArithmeticalUnitR_PartDeactivate ( )
		switchArithmeticalUnitR_PartSwitchOutput ( )
	
		
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
		
		getArithmeticalValue1R ( inout arithmeticalValueInout : int )
		getArithmeticalValue2R ( inout arithmeticalValueInout : int )
		
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
				useA1 => {getArithmeticalValue1R ( inout arithmeticalValueLocal ) }
				! useA1 =>  {getArithmeticalValue2R ( inout arithmeticalValueLocal ) } ;
			}			
			result := arithmeticalValueLocal;
		}
	}
	
		
	s1.senseSourceValueR = instantly in.getSourceValueP
	s2.senseSourceValueR = instantly in.getSourceValueP
	a1.getSensorValue1R = instantly s1:getSensorValueP
	a1.getSensorValue2R = instantly s2.getSensorValueP
	monitor.doSensorValuesMatchR = instantly a1.doSensorValuesMatchP	
	monitor.switchArithmeticalUnitR_PartActivate = instantly a2.activateP
	monitor.switchArithmeticalUnitR_PartDeactivate = instantly a1.deactivateP
	monitor.switchArithmeticalUnitR_PartSwitchOutput = instantly out.switchArithmeticalUnitP
	out.getArithmeticalValue1R = instantly a1.getArithmeticalValueP
	out.getArithmeticalValue2R = instantly a2.getArithmeticalValueP
	
	step {
		locals{}
		step in;
		step monitor;
		step out;
	}
}
