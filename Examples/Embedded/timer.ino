// IOs
// digital input
int resetTimerPin = 2;
// digital output
int triggerTimeoutPin = 3;

#define timeout 60
int currentTime = 0;
int resetTimerState;

void setup() {
  pinMode(triggerTimeoutPin, OUTPUT);
  pinMode(resetTimerPin, INPUT);
}
void loop() {
  resetTimerState = digitalRead(resetTimerPin);
  if (resetTimerState) {
    currentTime = 0;
  } else {
    currentTime += 1;
  }
  if (currentTime >= timeout) {
    digitalWrite(triggerTimeoutPin, HIGH);
  } else {
    digitalWrite(triggerTimeoutPin, LOW);
  }
  delay(1000);
}
