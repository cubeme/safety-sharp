// IOs
int sensorPin = 4; // input
int timerTriggeredPin = 5; // input
int resetTimerPin = 6; // output
int pumpPin = 7; // output

enum states { StateFilling=1, StateDraining=2, StateEmergencyStop=3 };
states currentState = StateFilling;
int sensorState;
int timerTriggeredState;
bool enablePump = false;
bool resetTimer = false;

void setup() {
  pinMode(sensorPin, INPUT);
  pinMode(timerTriggeredPin, INPUT);
  pinMode(resetTimerPin, OUTPUT);
  pinMode(pumpPin, OUTPUT);
}
void loop() {
  resetTimer = false;
  enablePump = false;
  sensorState = digitalRead(sensorPin);
  timerTriggeredState = digitalRead(timerTriggeredPin);
  switch (currentState) {
      case StateFilling:
        if (sensorState == HIGH) {
          currentState = StateDraining;
        } else if (timerTriggeredState == LOW) {
          enablePump = true;          
        } else if (timerTriggeredState == HIGH) {
          currentState=StateEmergencyStop;
        }
        break;
      case StateDraining:
        // Wait until Pressure is low enought
        if (sensorState == LOW) {
            resetTimer = true;
            currentState = StateFilling;
        }
        break;
      case StateEmergencyStop:
        break;
  }
  if (enablePump) {
    digitalWrite(pumpPin, HIGH);
  } else {
    digitalWrite(pumpPin, LOW);
  }
  if (resetTimer) {
    digitalWrite(resetTimerPin, HIGH);
  } else {
    digitalWrite(resetTimerPin, LOW);
  }
  delay(1000);
}
