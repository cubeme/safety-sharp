// IOs
int sensorPin = 4; // input
int pumpPin = 3; // output

#define timeout 60
int currentTime = 0;
enum states { StateFilling=1, StateDraining=2, StateEmergencyStop=3 };
states currentState = StateFilling;
int sensorState;
bool enablePump = false;

void setup() {
  pinMode(pumpPin, OUTPUT);
  pinMode(sensorPin, INPUT);
}
void loop() {
  sensorState = digitalRead(sensorPin);
  switch (currentState) {
      case StateFilling:
        if (sensorState == HIGH) {
          currentState = StateDraining;
          enablePump = false;
        } else if (currentTime <= timeout) {
          currentTime = currentTime + 1;
          enablePump = true;          
        } else if (currentTime > timeout) {
          currentState=StateEmergencyStop;
          enablePump = false;
        }
        break;
      case StateDraining:
        // Wait until Pressure is low enought
        if (sensorState == LOW) {
            currentTime = 0;
            enablePump = false;
            currentState = StateFilling;
        } else {
          enablePump = false;
        }
        break;
      case StateEmergencyStop:
        enablePump = false;
        break;
  }
  if (enablePump) {
    // turn the relay on (HIGH is the voltage level)
    digitalWrite(pumpPin, HIGH);
  } else {
    // turn the relay off by making the voltage LOW
    digitalWrite(pumpPin, LOW);
  }
  // wait for a second
  delay(1000);
}
