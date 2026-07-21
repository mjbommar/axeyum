pub fn handshake_step(state: u8, event: u8) -> u8 {
    if event == 2 {
        0
    } else if state == 0 && event == 0 {
        1
    } else if state == 1 && event == 1 {
        2
    } else {
        state
    }
}

pub fn handshake_step_bug(state: u8, event: u8) -> u8 {
    if state == 0 && event == 1 {
        3
    } else if event == 2 {
        0
    } else if state == 0 && event == 0 {
        1
    } else if state == 1 && event == 1 {
        2
    } else {
        state
    }
}
